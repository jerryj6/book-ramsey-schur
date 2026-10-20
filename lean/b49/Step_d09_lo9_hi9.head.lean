import BookRamsey.RowBridge
import BookRamsey.Inflate
import Lean
import Std.Tactic.BVDecide.LRAT.Parser

namespace BookRamsey.R49

open BookRamsey

private def parseCompressed (text : String) :
    Array Std.Tactic.BVDecide.LRAT.IntAction :=
  match Std.Tactic.BVDecide.LRAT.parseLRATProof
      (decodeGzipBase64 text) with
  | .error _ => #[]
  | .ok actions => actions

private def cert_d09_lo9_hi9 : Array Std.Tactic.BVDecide.LRAT.IntAction :=
  parseCompressed (include_str "../../../runs/b4b9/cert/d09_lo9_hi9.trimmed.lrat.gz.b64")

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem check_d09_lo9_hi9 :
    (let F := rcnf 27 4 9 9 9 9;
     Std.Tactic.BVDecide.LRAT.check cert_d09_lo9_hi9 F) = true := by
  native_decide

theorem exclude49_d09_lo9_hi9 :
    ∀ red : Fin 27 → Fin 27 → Bool,
      Symm red → BookFree red 4 9 →
      (∀ w : Fin 27, 9 ≤ redDeg red w ∧ redDeg red w ≤ 9) →
      ∀ v : Fin 27, redDeg red v ≠ 9 := by
  exact row_excl_of_check cert_d09_lo9_hi9 check_d09_lo9_hi9

end BookRamsey.R49
