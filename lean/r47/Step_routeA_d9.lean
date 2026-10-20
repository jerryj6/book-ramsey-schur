import BookRamsey.R47.Step_routeA_d9_Cubes
import BookRamsey.R47.Step_routeA_d9_Coverage
import BookRamsey.RowBridge

namespace BookRamsey.R47

open BookRamsey

theorem exclude_routeA_d9 :
    ∀ red : Fin 22 → Fin 22 → Bool,
      Symm red → BookFree red 4 7 →
      (∀ w : Fin 22, 9 ≤ redDeg red w ∧ redDeg red w ≤ 9) →
      ∀ v : Fin 22, redDeg red v ≠ 9 := by
  have hunit : ∀ c ∈ cubes_routeA_d9,
      (rcnf 22 4 7 9 9 9 ++ unitsOf c).Unsat := by
    intro c hc
    unfold cubes_routeA_d9 at hc
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact routeA_d9_b001_batch0_unsat [(59, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact routeA_d9_b006_batch0_unsat [(59, false), (23, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact routeA_d9_b001_batch0_unsat [(59, false), (23, true), (41, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact routeA_d9_b001_batch0_unsat [(59, false), (23, true), (41, false), (58, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact routeA_d9_b002_batch0_unsat [(59, false), (23, true), (41, false), (58, false), (69, true), (64, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact routeA_d9_b003_batch0_unsat [(59, false), (23, true), (41, false), (58, false), (69, true), (64, false), (82, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact routeA_d9_b006_batch0_unsat [(59, false), (23, true), (41, false), (58, false), (69, true), (64, false), (82, false)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact routeA_d9_b006_batch0_unsat [(59, false), (23, true), (41, false), (58, false), (69, false), (87, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    · exact routeA_d9_b004_batch0_unsat [(59, false), (23, true), (41, false), (58, false), (69, false), (87, false), (64, true)] (by decide)
    rcases (List.mem_cons.mp hc) with rfl | hc
    exact routeA_d9_b005_batch0_unsat [(59, false), (23, true), (41, false), (58, false), (69, false), (87, false), (64, false)] (by decide)
    all_goals cases hc
  apply row_excl_of_unsat
  exact BookRamsey.unsat_of_cubes (rcnf 22 4 7 9 9 9)
    cubes_routeA_d9 hunit unsat_routeA_d9_coverage

end BookRamsey.R47
