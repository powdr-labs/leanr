# Prompt: update powdr for the new apc-optimizer FFI (known VM + degree bound)

## Background

powdr calls the verified Lean `apc-optimizer` over FFI (crate
`powdr-autoprecompiles-lean-ffi`, wired into `powdr_autoprecompiles::optimizer::optimize`).
Today that path **hard-codes OpenVM** and **ignores the degree bound** — see the TODO in
`autoprecompiles/src/optimizer.rs`:

```rust
#[cfg(feature = "lean-optimizer")]
if lean::enabled() {
    // TODO: In addition to the field, the Lean optimizer also assumes the OpenVM
    // bus semantics with the default bus. It also ignores the degree bound.
    // Eventually, we should pass an argument encoding which known VM we're optimizing for.
    assert_eq!(
        T::known_field(),
        Some(KnownField::BabyBearField),
        "Lean optimizer only supports BabyBear"
    );
    let (optimized, next_free_id) =
        lean::optimize(&machine, bus_map, column_allocator.next_poly_id);
    column_allocator.next_poly_id = next_free_id;
    return Ok((optimized, column_allocator));
}
```

apc-optimizer has been changed so the FFI now **takes the target VM and the degree bound as
arguments** and dispatches to the OpenVM or SP1 optimizer accordingly. This prompt is to make the
matching change on the powdr side.

The apc-optimizer changes live on the (unmerged) branch:

- repo: `powdr-labs/apc-optimizer`
- branch: `claude/powdr-ffi-degree-bound-3q42q0`
- commit: `ce7b6ab0389a15fb0a4b2eb98941b3a5976bea21`

Point your apc-optimizer checkout (the one `powdr-autoprecompiles-lean-ffi/build.rs` builds via
`APC_OPTIMIZER_DIR`) at that commit for the powdr draft PR.

## The new FFI contract

The single Lean `@[export]` is still called `apc_optimizer_optimize_json`, but its C signature
changed from `(lean_object* input)` to:

```c
// vm: 0 = OpenVM (BabyBear), 1 = SP1 (KoalaBear)
lean_object* apc_optimizer_optimize_json(
    uint8_t vm,
    uint64_t degree_identities,
    uint64_t degree_bus_interactions,
    lean_object* input);
```

- `vm` selects the VM: apc-optimizer parses the export over that VM's field and runs its verified
  optimizer. An unknown discriminant yields `{"error": ...}`.
- `degree_identities` / `degree_bus_interactions` are the two components of the degree bound
  (max degree of algebraic identities, and of bus-interaction expressions). apc-optimizer no longer
  has a hard-coded default on this path — it uses exactly what you pass.
- `input` / return value: unchanged (`{"machine", "bus_map", "next_free_id"}` in, `{"machine",
  "next_free_id"}` or `{"error": ...}` out).

This maps 1:1 onto powdr's `DegreeBound` (`powdr_constraint_solver::inliner::DegreeBound`):

```rust
pub struct DegreeBound { pub identities: usize, pub bus_interactions: usize }
```

## Changes to make in powdr

### 1. C shim — `autoprecompiles-lean-ffi/c/ffi_shim.c`

Change the extern declaration of the Lean export and the public `apc_optimizer_optimize` wrapper to
thread the three new scalars through. The Lean-runtime init (`pthread_once`,
`initialize_apc_x2doptimizer_ApcOptimizer_Ffi`, thread registration) is **unchanged** — the module
is still `ApcOptimizer.Ffi`. Only the signature and the forwarded call change:

```c
extern lean_object *apc_optimizer_optimize_json(
    uint8_t vm, uint64_t degree_identities, uint64_t degree_bus_interactions,
    lean_object *input);

char *apc_optimizer_optimize(uint8_t vm, uint64_t degree_identities,
                             uint64_t degree_bus_interactions, const char *input) {
    ensure_init();                 // existing pthread_once + thread registration
    lean_object *lean_input = lean_mk_string(input);
    lean_object *out = apc_optimizer_optimize_json(
        vm, degree_identities, degree_bus_interactions, lean_input);
    const char *s = lean_string_cstr(out);
    char *result = strdup(s);
    lean_dec_ref(out);             // input is consumed by the Lean call, as before
    return result;
}
```

`apc_optimizer_free` is unchanged.

### 2. Rust wrapper — `autoprecompiles-lean-ffi/src/lib.rs`

Update the `extern "C"` block and `optimize_json`:

```rust
/// Which known VM to optimize for; discriminant must match apc-optimizer's `KnownVm`.
#[repr(u8)]
#[derive(Clone, Copy, Debug)]
pub enum KnownVm {
    OpenVm = 0,
    Sp1 = 1,
}

extern "C" {
    fn apc_optimizer_optimize(
        vm: u8,
        degree_identities: u64,
        degree_bus_interactions: u64,
        input: *const c_char,
    ) -> *mut c_char;
    fn apc_optimizer_free(p: *mut c_char);
}

pub fn optimize_json(
    vm: KnownVm,
    degree_identities: u64,
    degree_bus_interactions: u64,
    input: &str,
) -> Result<String, String> {
    let c_input = CString::new(input).map_err(|e| format!("input contains NUL byte: {e}"))?;
    let out_ptr = unsafe {
        apc_optimizer_optimize(vm as u8, degree_identities, degree_bus_interactions, c_input.as_ptr())
    };
    // ... rest unchanged (null check, CStr -> String, apc_optimizer_free, "{\"error\":" check) ...
}
```

### 3. The `lean` wrapper module in autoprecompiles

This is the module referenced as `lean::optimize` / `lean::enabled` in
`autoprecompiles/src/optimizer.rs`; it builds the JSON, calls
`powdr_autoprecompiles_lean_ffi::optimize_json`, and parses the result. The JSON format is
**unchanged** — only forward the new arguments. Give `lean::optimize` the VM and degree bound:

```rust
pub fn optimize<T: ...>(
    machine: &SymbolicMachine<T>,
    bus_map: &BusMap<...>,
    next_free_id: u64,
    vm: KnownVm,                 // from powdr_autoprecompiles_lean_ffi
    degree_bound: DegreeBound,
) -> (SymbolicMachine<T>, u64) {
    let input = /* existing serialization of machine + bus_map + next_free_id */;
    let out = powdr_autoprecompiles_lean_ffi::optimize_json(
        vm,
        degree_bound.identities as u64,
        degree_bound.bus_interactions as u64,
        &input,
    ).expect("apc-optimizer FFI failed");
    /* existing parse of `out` back into (SymbolicMachine, next_free_id) */
}
```

### 4. Call site — `autoprecompiles/src/optimizer.rs`

Replace the BabyBear-only assert with a VM derived from the field, and pass the real
`degree_bound` (already a parameter of `optimize`). Drop the stale TODO:

```rust
#[cfg(feature = "lean-optimizer")]
if lean::enabled() {
    let vm = match T::known_field() {
        Some(KnownField::BabyBearField) => KnownVm::OpenVm,
        Some(KnownField::KoalaBearField) => KnownVm::Sp1,
        other => panic!("Lean optimizer supports BabyBear (OpenVM) and KoalaBear (SP1), got {other:?}"),
    };
    let (optimized, next_free_id) =
        lean::optimize(&machine, bus_map, column_allocator.next_poly_id, vm, degree_bound);
    column_allocator.next_poly_id = next_free_id;
    return Ok((optimized, column_allocator));
}
```

(Confirm the exact `KnownField` variant name powdr uses for KoalaBear; the BabyBear one is
`KnownField::BabyBearField`. `KnownVm` comes from `powdr_autoprecompiles_lean_ffi`.)

## Notes

- VM ↔ field is 1:1 here: OpenVM uses BabyBear, SP1 uses KoalaBear, matching apc-optimizer's FFI
  dispatch (`0 → babyBear`, `1 → koalaBear`). Deriving the VM from `T::known_field()` needs no new
  parameter on powdr's public `optimize`.
- Keep the discriminant values in sync with apc-optimizer's `KnownVm` (`OpenVM = 0`, `SP1 = 1`,
  `ApcOptimizer/Ffi.lean`).

## Testing

- `cargo build -p powdr-autoprecompiles-lean-ffi` with `APC_OPTIMIZER_DIR` pointing at the pinned
  branch/commit (this triggers the `lake build`).
- Run the existing autoprecompiles tests with `--features lean-optimizer`; the OpenVM path must
  produce the same optimized machines as before (pass `DEFAULT_DEGREE_BOUND` = `{identities: 3,
  bus_interactions: 2}` for OpenVM, matching apc-optimizer's `OpenVM.defaultDegreeBound`).
