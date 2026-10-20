import Statement
import BookRamsey.R47.Peeling
import BookRamsey.R49.Peeling
import BookRamsey.B49Witness
import BookRamsey.R49.Step_d26_lo0_hi26
import BookRamsey.R49.Step_d25_lo0_hi26
import BookRamsey.R49.Step_d24_lo0_hi26
import BookRamsey.R49.Step_d23_lo0_hi26
import BookRamsey.R49.Step_d22_lo0_hi26
import BookRamsey.R49.Step_d21_lo0_hi26
import BookRamsey.R49.Step_d20_lo0_hi26
import BookRamsey.R49.Step_d19_lo0_hi26
import BookRamsey.R49.Step_d18_lo0_hi26
import BookRamsey.R49.Step_d17_lo0_hi26
import BookRamsey.R49.Step_d16_lo0_hi26
import BookRamsey.R49.Step_d15_lo0_hi26
import BookRamsey.R49.Step_d14_lo0_hi26
import BookRamsey.R49.Step_d13_lo0_hi26
import BookRamsey.R49.Step_d12_lo0_hi26
import BookRamsey.R49.Step_d11_lo0_hi26
import BookRamsey.R49.Step_d00_lo0_hi26
import BookRamsey.R49.Step_d01_lo0_hi26
import BookRamsey.R49.Step_d02_lo0_hi26
import BookRamsey.R49.Step_d03_lo0_hi26
import BookRamsey.R49.Step_d04_lo0_hi26
import BookRamsey.R49.Step_d05_lo0_hi26
import BookRamsey.R49.Step_d06_lo0_hi26
import BookRamsey.R49.Step_d07_lo7_hi10
import BookRamsey.R49.Step_d08_lo8_hi10
import BookRamsey.R49.Step_d10_lo9_hi10
import BookRamsey.R49.Step_d09_lo9_hi9

namespace BookRamsey.R49

open BookRamsey
open BookRamsey.R47

theorem R_B4_B9_le_27 : UpperBound 27 4 9 := by
  intro red hsymm hfree
  have hbounds0 : ∀ w : Fin 27, 0 ≤ redDeg red w ∧ redDeg red w ≤ 26 := by
    intro w
    exact ⟨Nat.zero_le _, redDeg_le_26 red w⟩

  have hno26 := exclude49_d26_lo0_hi26 red hsymm hfree hbounds0
  have hbounds0_25 :
      ∀ w : Fin 27, 0 ≤ redDeg red w ∧ redDeg red w ≤ 25 := by
    simpa using peel_high red hbounds0 hno26
  have hno25 := exclude49_d25_lo0_hi26 red hsymm hfree hbounds0
  have hbounds0_24 :
      ∀ w : Fin 27, 0 ≤ redDeg red w ∧ redDeg red w ≤ 24 := by
    simpa using peel_high red hbounds0_25 hno25
  have hno24 := exclude49_d24_lo0_hi26 red hsymm hfree hbounds0
  have hbounds0_23 :
      ∀ w : Fin 27, 0 ≤ redDeg red w ∧ redDeg red w ≤ 23 := by
    simpa using peel_high red hbounds0_24 hno24
  have hno23 := exclude49_d23_lo0_hi26 red hsymm hfree hbounds0
  have hbounds0_22 :
      ∀ w : Fin 27, 0 ≤ redDeg red w ∧ redDeg red w ≤ 22 := by
    simpa using peel_high red hbounds0_23 hno23
  have hno22 := exclude49_d22_lo0_hi26 red hsymm hfree hbounds0
  have hbounds0_21 :
      ∀ w : Fin 27, 0 ≤ redDeg red w ∧ redDeg red w ≤ 21 := by
    simpa using peel_high red hbounds0_22 hno22
  have hno21 := exclude49_d21_lo0_hi26 red hsymm hfree hbounds0
  have hbounds0_20 :
      ∀ w : Fin 27, 0 ≤ redDeg red w ∧ redDeg red w ≤ 20 := by
    simpa using peel_high red hbounds0_21 hno21
  have hno20 := exclude49_d20_lo0_hi26 red hsymm hfree hbounds0
  have hbounds0_19 :
      ∀ w : Fin 27, 0 ≤ redDeg red w ∧ redDeg red w ≤ 19 := by
    simpa using peel_high red hbounds0_20 hno20
  have hno19 := exclude49_d19_lo0_hi26 red hsymm hfree hbounds0
  have hbounds0_18 :
      ∀ w : Fin 27, 0 ≤ redDeg red w ∧ redDeg red w ≤ 18 := by
    simpa using peel_high red hbounds0_19 hno19
  have hno18 := exclude49_d18_lo0_hi26 red hsymm hfree hbounds0
  have hbounds0_17 :
      ∀ w : Fin 27, 0 ≤ redDeg red w ∧ redDeg red w ≤ 17 := by
    simpa using peel_high red hbounds0_18 hno18
  have hno17 := exclude49_d17_lo0_hi26 red hsymm hfree hbounds0
  have hbounds0_16 :
      ∀ w : Fin 27, 0 ≤ redDeg red w ∧ redDeg red w ≤ 16 := by
    simpa using peel_high red hbounds0_17 hno17
  have hno16 := exclude49_d16_lo0_hi26 red hsymm hfree hbounds0
  have hbounds0_15 :
      ∀ w : Fin 27, 0 ≤ redDeg red w ∧ redDeg red w ≤ 15 := by
    simpa using peel_high red hbounds0_16 hno16
  have hno15 := exclude49_d15_lo0_hi26 red hsymm hfree hbounds0
  have hbounds0_14 :
      ∀ w : Fin 27, 0 ≤ redDeg red w ∧ redDeg red w ≤ 14 := by
    simpa using peel_high red hbounds0_15 hno15
  have hno14 := exclude49_d14_lo0_hi26 red hsymm hfree hbounds0
  have hbounds0_13 :
      ∀ w : Fin 27, 0 ≤ redDeg red w ∧ redDeg red w ≤ 13 := by
    simpa using peel_high red hbounds0_14 hno14
  have hno13 := exclude49_d13_lo0_hi26 red hsymm hfree hbounds0
  have hbounds0_12 :
      ∀ w : Fin 27, 0 ≤ redDeg red w ∧ redDeg red w ≤ 12 := by
    simpa using peel_high red hbounds0_13 hno13
  have hno12 := exclude49_d12_lo0_hi26 red hsymm hfree hbounds0
  have hbounds0_11 :
      ∀ w : Fin 27, 0 ≤ redDeg red w ∧ redDeg red w ≤ 11 := by
    simpa using peel_high red hbounds0_12 hno12
  have hno11 := exclude49_d11_lo0_hi26 red hsymm hfree hbounds0
  have hbounds0_10 :
      ∀ w : Fin 27, 0 ≤ redDeg red w ∧ redDeg red w ≤ 10 := by
    simpa using peel_high red hbounds0_11 hno11

  have hno0 := exclude49_d00_lo0_hi26 red hsymm hfree hbounds0
  have hbounds1_10 :
      ∀ w : Fin 27, 1 ≤ redDeg red w ∧ redDeg red w ≤ 10 := by
    simpa using peel_low red hbounds0_10 hno0
  have hno1 := exclude49_d01_lo0_hi26 red hsymm hfree hbounds0
  have hbounds2_10 :
      ∀ w : Fin 27, 2 ≤ redDeg red w ∧ redDeg red w ≤ 10 := by
    simpa using peel_low red hbounds1_10 hno1
  have hno2 := exclude49_d02_lo0_hi26 red hsymm hfree hbounds0
  have hbounds3_10 :
      ∀ w : Fin 27, 3 ≤ redDeg red w ∧ redDeg red w ≤ 10 := by
    simpa using peel_low red hbounds2_10 hno2
  have hno3 := exclude49_d03_lo0_hi26 red hsymm hfree hbounds0
  have hbounds4_10 :
      ∀ w : Fin 27, 4 ≤ redDeg red w ∧ redDeg red w ≤ 10 := by
    simpa using peel_low red hbounds3_10 hno3
  have hno4 := exclude49_d04_lo0_hi26 red hsymm hfree hbounds0
  have hbounds5_10 :
      ∀ w : Fin 27, 5 ≤ redDeg red w ∧ redDeg red w ≤ 10 := by
    simpa using peel_low red hbounds4_10 hno4
  have hno5 := exclude49_d05_lo0_hi26 red hsymm hfree hbounds0
  have hbounds6_10 :
      ∀ w : Fin 27, 6 ≤ redDeg red w ∧ redDeg red w ≤ 10 := by
    simpa using peel_low red hbounds5_10 hno5
  have hno6 := exclude49_d06_lo0_hi26 red hsymm hfree hbounds0
  have hbounds7_10 :
      ∀ w : Fin 27, 7 ≤ redDeg red w ∧ redDeg red w ≤ 10 := by
    simpa using peel_low red hbounds6_10 hno6

  have hno7 := exclude49_d07_lo7_hi10 red hsymm hfree hbounds7_10
  have hbounds8_10 :
      ∀ w : Fin 27, 8 ≤ redDeg red w ∧ redDeg red w ≤ 10 := by
    simpa using peel_low red hbounds7_10 hno7
  have hno8 := exclude49_d08_lo8_hi10 red hsymm hfree hbounds8_10
  have hbounds9_10 :
      ∀ w : Fin 27, 9 ≤ redDeg red w ∧ redDeg red w ≤ 10 := by
    simpa using peel_low red hbounds8_10 hno8
  have hno10 := exclude49_d10_lo9_hi10 red hsymm hfree hbounds9_10
  have hbounds9_9 :
      ∀ w : Fin 27, 9 ≤ redDeg red w ∧ redDeg red w ≤ 9 := by
    simpa using peel_high red hbounds9_10 hno10
  have hno9 := exclude49_d09_lo9_hi9 red hsymm hfree hbounds9_9
  have v : Fin 27 := ⟨0, by decide⟩
  have hv : redDeg red v = 9 := by
    rcases hbounds9_9 v with ⟨hlo, hhi⟩
    omega
  exact hno9 v hv

theorem R_B4_B9_lower : LowerBound 26 4 9 := b49_lower

theorem R_B4_B9_eq : LowerBound 26 4 9 ∧ UpperBound 27 4 9 :=
  ⟨R_B4_B9_lower, R_B4_B9_le_27⟩

end BookRamsey.R49

#print axioms BookRamsey.R49.R_B4_B9_le_27
#print axioms BookRamsey.R49.R_B4_B9_eq
