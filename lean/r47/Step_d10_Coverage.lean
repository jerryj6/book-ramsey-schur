import BookRamsey.R47.Step_d10_Cubes
import BookRamsey.RowBridge
import BookRamsey.Inflate
import Lean
import Std.Tactic.BVDecide.LRAT.Parser

namespace BookRamsey.R47

open BookRamsey

private def parseCompressed (text : String) :
    Array Std.Tactic.BVDecide.LRAT.IntAction :=
  match Std.Tactic.BVDecide.LRAT.parseLRATProof
      (decodeGzipBase64 text) with
  | .error _ => #[]
  | .ok actions => actions

private def cert_d10_coverage : Array Std.Tactic.BVDecide.LRAT.IntAction :=
  parseCompressed (include_str "../../../runs/rowcnf47/d10_coverage_current/coverage.trimmed.lrat.gz.b64")

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem check_d10_coverage :
    Std.Tactic.BVDecide.LRAT.check cert_d10_coverage
      (rcnf 22 4 7 10 7 10 ++ negCubes cubes_d10) = true := by
  native_decide

theorem unsat_d10_coverage :
    (rcnf 22 4 7 10 7 10 ++ negCubes cubes_d10).Unsat :=
  Std.Tactic.BVDecide.LRAT.check_sound cert_d10_coverage _ check_d10_coverage

end BookRamsey.R47
