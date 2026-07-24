import VersoManual

open Verso.Genre.Manual

/-! Bibliographic references, cited from `Docs.lean`. Verso renders each cite inline as
    author–year and drops the full entry in the margin. Verso's `Article` type is used for
    whitepapers and ePrint reports (`journal` carries the venue label; `volume`/`number` left
    empty). -/

namespace Docs

def powdr : Article where
  title := inlines!"powdr: a modular stack for zkVMs and proof systems"
  authors := #[inlines!"powdr"]
  journal := inlines!"Software, https://github.com/powdr-labs/powdr"
  year := 2024
  month := none
  volume := inlines!""
  number := inlines!""
  url := some "https://www.powdr.org/"

def openVM : Article where
  title := inlines!"OpenVM Whitepaper"
  authors := #[inlines!"OpenVM"]
  journal := inlines!"Whitepaper"
  year := 2026
  month := none
  volume := inlines!""
  number := inlines!""
  url := some "https://openvm.dev/whitepaper.pdf"

def sp1 : Article where
  title := inlines!"SP1: a performant, open-source zkVM for RISC-V"
  authors := #[inlines!"Succinct"]
  journal := inlines!"Software, https://github.com/succinctlabs/sp1"
  year := 2024
  month := none
  volume := inlines!""
  number := inlines!""
  url := some "https://github.com/succinctlabs/sp1"

def sp1Jagged : Article where
  title := inlines!"Jagged Polynomial Commitments (or: How to Stack Multilinears)"
  authors := #[inlines!"Tamir Hemo", inlines!"Kevin Jue", inlines!"Eugene Rabinovich",
    inlines!"Gyumin Roh", inlines!"Ron D. Rothblum"]
  journal := inlines!"Cryptology ePrint Archive, Paper 2025/917"
  year := 2025
  month := none
  volume := inlines!""
  number := inlines!""
  url := some "https://eprint.iacr.org/2025/917"

def plonk : Article where
  title := inlines!"PLONK: Permutations over Lagrange-bases for Oecumenical Noninteractive arguments of Knowledge"
  authors := #[inlines!"Ariel Gabizon", inlines!"Zachary J. Williamson", inlines!"Oana Ciobotaru"]
  journal := inlines!"Cryptology ePrint Archive, Paper 2019/953"
  year := 2019
  month := none
  volume := inlines!""
  number := inlines!""
  url := some "https://eprint.iacr.org/2019/953"

def stark : Article where
  title := inlines!"Scalable, transparent, and post-quantum secure computational integrity"
  authors := #[inlines!"Eli Ben-Sasson", inlines!"Iddo Bentov", inlines!"Yinon Horesh",
    inlines!"Michael Riabzev"]
  journal := inlines!"Cryptology ePrint Archive, Paper 2018/046"
  year := 2018
  month := none
  volume := inlines!""
  number := inlines!""
  url := some "https://eprint.iacr.org/2018/046"

def logup : Article where
  title := inlines!"Multivariate lookups based on logarithmic derivatives"
  authors := #[inlines!"Ulrich Haböck"]
  journal := inlines!"Cryptology ePrint Archive, Paper 2022/1530"
  year := 2022
  month := none
  volume := inlines!""
  number := inlines!""
  url := some "https://eprint.iacr.org/2022/1530"

def logupGKR : Article where
  title := inlines!"Improving logarithmic derivative lookups using GKR"
  authors := #[inlines!"Shahar Papini", inlines!"Ulrich Haböck"]
  journal := inlines!"Cryptology ePrint Archive, Paper 2023/1284"
  year := 2023
  month := none
  volume := inlines!""
  number := inlines!""
  url := some "https://eprint.iacr.org/2023/1284"

def plookup : Article where
  title := inlines!"plookup: A simplified polynomial protocol for lookup tables"
  authors := #[inlines!"Ariel Gabizon", inlines!"Zachary J. Williamson"]
  journal := inlines!"Cryptology ePrint Archive, Paper 2020/315"
  year := 2020
  month := none
  volume := inlines!""
  number := inlines!""
  url := some "https://eprint.iacr.org/2020/315"

def blum : Article where
  title := inlines!"Checking the Correctness of Memories"
  authors := #[inlines!"Manuel Blum", inlines!"William S. Evans", inlines!"Peter Gemmell",
    inlines!"Sampath Kannan", inlines!"Moni Naor"]
  journal := inlines!"Algorithmica"
  year := 1994
  month := none
  volume := inlines!"12"
  number := inlines!"2"
  pages := some (225, 244)
  url := some "https://doi.org/10.1007/BF01185212"

def twistShout : Article where
  title := inlines!"Twist and Shout: Faster memory checking arguments via one-hot addressing and increments"
  authors := #[inlines!"Srinath Setty", inlines!"Justin Thaler"]
  journal := inlines!"Cryptology ePrint Archive, Paper 2025/105"
  year := 2025
  month := none
  volume := inlines!""
  number := inlines!""
  url := some "https://eprint.iacr.org/2025/105"

end Docs
