# Docs: the audited-surface site

A [Verso](https://github.com/leanprover/verso) document that renders the audited surface of
`apc-optimizer` as a single-page, cross-linked site. Prose is interleaved with the real
definitions and theorem statements, spliced live from the compiled source via `{docstring}` — so
the formal content shown *is* the machine-checked artifact, not a transcription.

- `Docs.lean` — the document (prose + `{docstring}` splices).
- `Docs/Bibliography.lean` — the cited references.
- `assets/trust.dot` — the trust-map figure (rendered to `assets/trust.svg` by the build script).

It is a **non-default** lake target, so `lake build` and CI never build it.

## Build and serve locally

```bash
docs/build.sh --serve
```

This renders the figure, builds the doc, writes the site to `docs/_out/html-single`, and serves it
at <http://127.0.0.1:8017>. Open that URL in a browser.

Serving over HTTP is **required** — opening `index.html` as a `file://` URL breaks the hover
tooltips and search, which fetch JSON at runtime.

To build without serving, run `docs/build.sh` and point any static file server at
`docs/_out/html-single` (e.g. `python3 -m http.server -d docs/_out/html-single`).

The first build compiles the Verso toolchain and is slow; subsequent builds are fast (only the
document recompiles).
