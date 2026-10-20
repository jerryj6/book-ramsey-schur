import BookRamsey.R47.Peeling

namespace BookRamsey.R49

open BookRamsey

theorem redDeg_le_26 (red : Fin 27 → Fin 27 → Bool) (w : Fin 27) :
    redDeg red w ≤ 26 := by
  have hcount : redDeg red w =
      countTrue (rowDegreeBits red w.val false) := by
    simpa using (rowDegreeBits_red_count red w.val w.isLt).symm
  rw [hcount]
  calc
    countTrue (rowDegreeBits red w.val false) ≤
        (rowDegreeBits red w.val false).length := countTrue_le_length _
    _ = 26 := by simp [rowDegreeBits, rowOtherVertices_length w.val w.isLt]

end BookRamsey.R49
