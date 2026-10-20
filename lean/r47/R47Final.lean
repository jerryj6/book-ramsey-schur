import Statement
import BookRamsey.R47.Peeling
import BookRamsey.R47.Step_d0_lo0_hi21
import BookRamsey.R47.Step_d1_lo0_hi21
import BookRamsey.R47.Step_d2_lo0_hi21
import BookRamsey.R47.Step_d3_lo0_hi21
import BookRamsey.R47.Step_d4_lo0_hi21
import BookRamsey.R47.Step_d5_lo0_hi21
import BookRamsey.R47.Step_d6_lo6_hi10
import BookRamsey.R47.Step_d10
import BookRamsey.R47.Step_d11_lo6_hi11
import BookRamsey.R47.Step_d12_lo6_hi12
import BookRamsey.R47.Step_d13_lo6_hi13
import BookRamsey.R47.Step_d14_lo0_hi21
import BookRamsey.R47.Step_d15_lo0_hi21
import BookRamsey.R47.Step_d16_lo0_hi21
import BookRamsey.R47.Step_d17_lo0_hi21
import BookRamsey.R47.Step_d18_lo0_hi21
import BookRamsey.R47.Step_d19_lo0_hi21
import BookRamsey.R47.Step_d20_lo0_hi21
import BookRamsey.R47.Step_d21_lo0_hi21
import BookRamsey.R47.Step_routeA_d7
import BookRamsey.R47.Step_routeA_d8
import BookRamsey.R47.Step_routeA_d9
import BookRamsey.LMPVWitness

namespace BookRamsey.R47

open BookRamsey

theorem R_B4_B7_le_22 : UpperBound 22 4 7 := by
  intro red hsymm hfree
  have hbounds0 : ∀ w : Fin 22, 0 ≤ redDeg red w ∧ redDeg red w ≤ 21 := by
    intro w
    exact ⟨Nat.zero_le _, redDeg_le_21 red w⟩

  have hno0 := exclude_d0_lo0_hi21 red hsymm hfree hbounds0
  have hbounds1 : ∀ w : Fin 22, 1 ≤ redDeg red w ∧ redDeg red w ≤ 21 := by
    simpa using peel_low red hbounds0 hno0
  have hno1 := exclude_d1_lo0_hi21 red hsymm hfree hbounds0
  have hbounds2 : ∀ w : Fin 22, 2 ≤ redDeg red w ∧ redDeg red w ≤ 21 := by
    simpa using peel_low red hbounds1 hno1
  have hno2 := exclude_d2_lo0_hi21 red hsymm hfree hbounds0
  have hbounds3 : ∀ w : Fin 22, 3 ≤ redDeg red w ∧ redDeg red w ≤ 21 := by
    simpa using peel_low red hbounds2 hno2
  have hno3 := exclude_d3_lo0_hi21 red hsymm hfree hbounds0
  have hbounds4 : ∀ w : Fin 22, 4 ≤ redDeg red w ∧ redDeg red w ≤ 21 := by
    simpa using peel_low red hbounds3 hno3
  have hno4 := exclude_d4_lo0_hi21 red hsymm hfree hbounds0
  have hbounds5 : ∀ w : Fin 22, 5 ≤ redDeg red w ∧ redDeg red w ≤ 21 := by
    simpa using peel_low red hbounds4 hno4
  have hno5 := exclude_d5_lo0_hi21 red hsymm hfree hbounds0
  have hbounds6_21 :
      ∀ w : Fin 22, 6 ≤ redDeg red w ∧ redDeg red w ≤ 21 := by
    simpa using peel_low red hbounds5 hno5

  have hno21 := exclude_d21_lo0_hi21 red hsymm hfree hbounds0
  have hbounds6_20 :
      ∀ w : Fin 22, 6 ≤ redDeg red w ∧ redDeg red w ≤ 20 := by
    simpa using peel_high red hbounds6_21 hno21
  have hno20 := exclude_d20_lo0_hi21 red hsymm hfree hbounds0
  have hbounds6_19 :
      ∀ w : Fin 22, 6 ≤ redDeg red w ∧ redDeg red w ≤ 19 := by
    simpa using peel_high red hbounds6_20 hno20
  have hno19 := exclude_d19_lo0_hi21 red hsymm hfree hbounds0
  have hbounds6_18 :
      ∀ w : Fin 22, 6 ≤ redDeg red w ∧ redDeg red w ≤ 18 := by
    simpa using peel_high red hbounds6_19 hno19
  have hno18 := exclude_d18_lo0_hi21 red hsymm hfree hbounds0
  have hbounds6_17 :
      ∀ w : Fin 22, 6 ≤ redDeg red w ∧ redDeg red w ≤ 17 := by
    simpa using peel_high red hbounds6_18 hno18
  have hno17 := exclude_d17_lo0_hi21 red hsymm hfree hbounds0
  have hbounds6_16 :
      ∀ w : Fin 22, 6 ≤ redDeg red w ∧ redDeg red w ≤ 16 := by
    simpa using peel_high red hbounds6_17 hno17
  have hno16 := exclude_d16_lo0_hi21 red hsymm hfree hbounds0
  have hbounds6_15 :
      ∀ w : Fin 22, 6 ≤ redDeg red w ∧ redDeg red w ≤ 15 := by
    simpa using peel_high red hbounds6_16 hno16
  have hno15 := exclude_d15_lo0_hi21 red hsymm hfree hbounds0
  have hbounds6_14 :
      ∀ w : Fin 22, 6 ≤ redDeg red w ∧ redDeg red w ≤ 14 := by
    simpa using peel_high red hbounds6_15 hno15
  have hno14 := exclude_d14_lo0_hi21 red hsymm hfree hbounds0
  have hbounds6_13 :
      ∀ w : Fin 22, 6 ≤ redDeg red w ∧ redDeg red w ≤ 13 := by
    simpa using peel_high red hbounds6_14 hno14

  have hno13 := exclude_d13_lo6_hi13 red hsymm hfree hbounds6_13
  have hbounds6_12 :
      ∀ w : Fin 22, 6 ≤ redDeg red w ∧ redDeg red w ≤ 12 := by
    simpa using peel_high red hbounds6_13 hno13
  have hno12 := exclude_d12_lo6_hi12 red hsymm hfree hbounds6_12
  have hbounds6_11 :
      ∀ w : Fin 22, 6 ≤ redDeg red w ∧ redDeg red w ≤ 11 := by
    simpa using peel_high red hbounds6_12 hno12
  have hno11 := exclude_d11_lo6_hi11 red hsymm hfree hbounds6_11
  have hbounds6_10 :
      ∀ w : Fin 22, 6 ≤ redDeg red w ∧ redDeg red w ≤ 10 := by
    simpa using peel_high red hbounds6_11 hno11

  have hno6 := exclude_d6_lo6_hi10 red hsymm hfree hbounds6_10
  have hbounds7_10 :
      ∀ w : Fin 22, 7 ≤ redDeg red w ∧ redDeg red w ≤ 10 := by
    simpa using peel_low red hbounds6_10 hno6
  have hno10 := exclude_d10 red hsymm hfree hbounds7_10
  have hbounds7_9 :
      ∀ w : Fin 22, 7 ≤ redDeg red w ∧ redDeg red w ≤ 9 := by
    simpa using peel_high red hbounds7_10 hno10

  have hno7 := exclude_routeA_d7 red hsymm hfree hbounds7_9
  have hbounds8_9 :
      ∀ w : Fin 22, 8 ≤ redDeg red w ∧ redDeg red w ≤ 9 := by
    simpa using peel_low red hbounds7_9 hno7
  have hno8 := exclude_routeA_d8 red hsymm hfree hbounds8_9
  have hbounds9_9 :
      ∀ w : Fin 22, 9 ≤ redDeg red w ∧ redDeg red w ≤ 9 := by
    simpa using peel_low red hbounds8_9 hno8
  have hno9 := exclude_routeA_d9 red hsymm hfree hbounds9_9
  have v : Fin 22 := ⟨0, by decide⟩
  have hv : redDeg red v = 9 := by
    rcases hbounds9_9 v with ⟨hlo, hhi⟩
    omega
  exact hno9 v hv

theorem R_B4_B7_lower_21 : LowerBound 21 4 7 :=
  BookRamsey.lmpv_lower_bound

theorem R_B4_B7_eq : LowerBound 21 4 7 ∧ UpperBound 22 4 7 :=
  ⟨R_B4_B7_lower_21, R_B4_B7_le_22⟩

end BookRamsey.R47

#print axioms BookRamsey.R47.R_B4_B7_le_22
#print axioms BookRamsey.R47.R_B4_B7_lower_21
#print axioms BookRamsey.R47.R_B4_B7_eq
