import BookRamsey.RowBridge

namespace BookRamsey.R47

open BookRamsey

theorem peel_lo {N : Nat} (red : Fin N → Fin N → Bool) {lo hi : Nat}
    (hbounds : ∀ w, lo ≤ redDeg red w ∧ redDeg red w ≤ hi)
    (hno : ∀ w, redDeg red w ≠ lo) :
    ∀ w, lo + 1 ≤ redDeg red w ∧ redDeg red w ≤ hi := by
  intro w
  rcases hbounds w with ⟨hlo, hhi⟩
  have hne := hno w
  exact ⟨by omega, hhi⟩

theorem peel_hi {N : Nat} (red : Fin N → Fin N → Bool) {lo hi : Nat}
    (hbounds : ∀ w, lo ≤ redDeg red w ∧ redDeg red w ≤ hi)
    (hno : ∀ w, redDeg red w ≠ hi) :
    ∀ w, lo ≤ redDeg red w ∧ redDeg red w ≤ hi - 1 := by
  intro w
  rcases hbounds w with ⟨hlo, hhi⟩
  have hne := hno w
  exact ⟨hlo, by omega⟩

theorem peel_low {N : Nat} (red : Fin N → Fin N → Bool) {lo hi : Nat}
    (hbounds : ∀ w, lo ≤ redDeg red w ∧ redDeg red w ≤ hi)
    (hno : ∀ w, redDeg red w ≠ lo) :
    ∀ w, lo + 1 ≤ redDeg red w ∧ redDeg red w ≤ hi :=
  peel_lo red hbounds hno

theorem peel_high {N : Nat} (red : Fin N → Fin N → Bool) {lo hi : Nat}
    (hbounds : ∀ w, lo ≤ redDeg red w ∧ redDeg red w ≤ hi)
    (hno : ∀ w, redDeg red w ≠ hi) :
    ∀ w, lo ≤ redDeg red w ∧ redDeg red w ≤ hi - 1 :=
  peel_hi red hbounds hno

theorem redDeg_le_21 (red : Fin 22 → Fin 22 → Bool) (w : Fin 22) :
    redDeg red w ≤ 21 := by
  have hcount : redDeg red w =
      countTrue (rowDegreeBits red w.val false) := by
    simpa using (rowDegreeBits_red_count red w.val w.isLt).symm
  rw [hcount]
  calc
    countTrue (rowDegreeBits red w.val false) ≤
        (rowDegreeBits red w.val false).length := countTrue_le_length _
    _ = 21 := by simp [rowDegreeBits, rowOtherVertices_length w.val w.isLt]

end BookRamsey.R47
