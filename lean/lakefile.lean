import Lake
open Lake DSL

/-!
Lake scaffold for the Lean formalization.

IMPORTANT — scaffold, not the original build file: the campaign's lakefile and
part of the module tree were lost before release (see `docs/LEAN_STATUS.md`).
This file records the intended project shape — the same layout convention as the
sibling release `jerryj6/erdos-616-t21` (mathlib pinned at the same revision).
It will NOT build until the missing modules are restored.

* `BookRamseyCheckers`: executable checkers in Lean core (no Mathlib),
  `precompileModules` so `native_decide` certificate checks run native code.
* `BookRamsey`: the mathematics plus the certificate-carrying Step_* modules
  (which embed `*.lrat.gz.b64` payloads via `include_str`; the payloads are
  produced from the archived `.lrat.gz` certificates — see `sat/batch_verify.sh`
  and `docs/LEAN_STATUS.md`).
* `Schur`: the Ahmed–Schaal formalization (statement, symbolic encoding,
  certificate modules `Schur.DirCerts`/`Schur.SymCert*` — currently missing).
-/

package bookramsey where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "56a005855ea17e0b0958f73ec801ae140b0a1679"

lean_lib BookRamseyCheckers where
  precompileModules := true

@[default_target]
lean_lib BookRamsey where

lean_lib Schur where
