import Mathlib
import Schur.SchurStatement
import Schur.SymSound

namespace Schur

def bitColor (b : Bool) : Fin 3 :=
  if b then symColorOfNat 1 else symColorOfNat 0

def smallColor (bits : List Bool) (x : Nat) : Fin 3 :=
  bitColor (bits.getD (x - 1) false)

def boundedLists (N : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | k + 1 =>
    (List.range N).flatMap fun i =>
      (boundedLists N k).map fun l => (i + 1) :: l

theorem mem_boundedLists_of_bounds
    {N k : Nat} {l : List Nat}
    (hlen : l.length = k)
    (hitems : ∀ x, x ∈ l → 1 ≤ x ∧ x ≤ N) :
    l ∈ boundedLists N k := by
  induction k generalizing l with
  | zero =>
    have hl : l = [] := by simpa using hlen
    subst l
    simp [boundedLists]
  | succ k ih =>
    cases l with
    | nil => simp at hlen
    | cons x xs =>
      have hlen' : xs.length = k := by simp at hlen; omega
      have hx := hitems x (by simp)
      have htail : ∀ y, y ∈ xs → 1 ≤ y ∧ y ≤ N := by
        intro y hy
        exact hitems y (by simp [hy])
      apply List.mem_flatMap.mpr
      refine ⟨x - 1, List.mem_range.mpr (by omega), ?_⟩
      apply List.mem_map.mpr
      refine ⟨xs, ih hlen' htail, ?_⟩
      simp [Nat.sub_add_cancel hx.1]

def tupleIsSolution (bits : List Bool) (color : Bool)
    (summands : List Nat) : Bool :=
  decide (summands.sum ≤ bits.length) &&
    summands.all (fun x => bits.getD (x - 1) false == color) &&
    (bits.getD (summands.sum - 1) false == color)

def hasSmallSolution (bits : List Bool) (k : Nat) (color : Bool) : Bool :=
  (boundedLists bits.length (k - 1)).any
    (tupleIsSolution bits color)

def smallColoringValid (s t M : Nat) (bits : List Bool) : Bool :=
  decide (bits.length = M - 1) &&
    !(hasSmallSolution bits s false) &&
    !(hasSmallSolution bits t true)

theorem bitColor_injective {a b : Bool}
    (h : bitColor a = bitColor b) : a = b := by
  cases a <;> cases b <;> simp [bitColor, symColorOfNat] at h ⊢

theorem bitColor_ne_two (b : Bool) :
    bitColor b ≠ symColorOfNat 2 := by
  cases b <;> simp [bitColor, symColorOfNat_ne_02, symColorOfNat_ne_12]

theorem smallColoring_hasSolution_of_monoSol
    {bits : List Bool} {N k : Nat} {color : Bool}
    (hN : bits.length = N)
    (hsol : MonoSol N k (smallColor bits) (bitColor color)) :
    hasSmallSolution bits k color = true := by
  rcases hsol with ⟨summands, hlen, hitems, hsumPos, hsumLe, htarget⟩
  have hitems' : ∀ x, x ∈ summands → 1 ≤ x ∧ x ≤ N := by
    intro x hx
    exact ⟨(hitems x hx).1, (hitems x hx).2.1⟩
  have hmem : summands ∈ boundedLists N (k - 1) :=
    mem_boundedLists_of_bounds hlen hitems'
  have hbits : ∀ x, x ∈ summands →
      bits.getD (x - 1) false = color := by
    intro x hx
    have hcolor := (hitems x hx).2.2
    exact bitColor_injective (by simpa [smallColor] using hcolor)
  have htargetBits : bits.getD (summands.sum - 1) false = color :=
    bitColor_injective (by simpa [smallColor] using htarget)
  have hsumLeBits : summands.sum ≤ bits.length := by rw [hN]; exact hsumLe
  have htuple : tupleIsSolution bits color summands = true := by
    unfold tupleIsSolution
    apply Bool.and_eq_true_iff.mpr
    constructor
    · apply Bool.and_eq_true_iff.mpr
      constructor
      · simp [hsumLeBits]
      · apply List.all_eq_true.mpr
        intro x hx
        exact beq_iff_eq.mpr (hbits x hx)
    · exact beq_iff_eq.mpr htargetBits
  rw [hasSmallSolution, List.any_eq_true]
  exact ⟨summands, by simpa [hN] using hmem, htuple⟩

theorem smallColoring_avoids_zero
    {s t M : Nat} {bits : List Bool}
    (hvalid : smallColoringValid s t M bits = true) :
    ¬ MonoSol (M - 1) s (smallColor bits) (bitColor false) := by
  intro hsol
  unfold smallColoringValid at hvalid
  rcases Bool.and_eq_true_iff.mp hvalid with ⟨hfirst, _⟩
  rcases Bool.and_eq_true_iff.mp hfirst with ⟨hLen, hnot⟩
  have hN : bits.length = M - 1 := of_decide_eq_true hLen
  have hfalse : hasSmallSolution bits s false = false := by
    cases h : hasSmallSolution bits s false <;> simp_all
  have htrue := smallColoring_hasSolution_of_monoSol hN hsol
  rw [hfalse] at htrue
  cases htrue

theorem smallColoring_avoids_one
    {s t M : Nat} {bits : List Bool}
    (hvalid : smallColoringValid s t M bits = true) :
    ¬ MonoSol (M - 1) t (smallColor bits) (bitColor true) := by
  intro hsol
  unfold smallColoringValid at hvalid
  have hLen : bits.length = M - 1 := by
    rcases Bool.and_eq_true_iff.mp hvalid with ⟨hfirst, _⟩
    rcases Bool.and_eq_true_iff.mp hfirst with ⟨hlen, _⟩
    exact of_decide_eq_true hlen
  have hfalse : hasSmallSolution bits t true = false := by
    cases h : hasSmallSolution bits t true <;> simp_all
  have htrue := smallColoring_hasSolution_of_monoSol hLen hsol
  rw [hfalse] at htrue
  cases htrue

def bits44 : List Bool :=
  [true, true, false, false, false, false, false, false, true, true]

def bits45 : List Bool :=
  [false, false, true, true, true, true, true, true, true, true, true,
    false, false]

def bits46 : List Bool :=
  [false, false, true, true, true, true, true, true, true, true, true,
    true, true, true, false, false]

def bits55 : List Bool :=
  [true, true, true, false, false, false, false, false, false, false,
    false, false, false, false, false, true, true, true]

set_option maxHeartbeats 0 in
theorem smallColoringValid_44 :
    smallColoringValid 4 4 11 bits44 = true := by
  native_decide

set_option maxHeartbeats 0 in
theorem smallColoringValid_45 :
    smallColoringValid 4 5 14 bits45 = true := by
  native_decide

set_option maxHeartbeats 0 in
theorem smallColoringValid_46 :
    smallColoringValid 4 6 17 bits46 = true := by
  native_decide

set_option maxHeartbeats 0 in
theorem smallColoringValid_55 :
    smallColoringValid 5 5 19 bits55 = true := by
  native_decide

def adjustTop (d x : Nat) : Nat :=
  if d ≤ x then x - d + 1 else x

def topCount (d : Nat) : List Nat → Nat
  | [] => 0
  | x :: xs => (if d ≤ x then 1 else 0) + topCount d xs

theorem topCount_pos_of_mem
    {d x : Nat} {xs : List Nat}
    (hmem : x ∈ xs) (htop : d ≤ x) :
    0 < topCount d xs := by
  induction xs with
  | nil => simp at hmem
  | cons y ys ih =>
    simp only [List.mem_cons] at hmem
    by_cases hy : d ≤ y
    · simp [topCount, hy]
    · simp [topCount, hy]
      rcases hmem with hxy | hmem
      · subst y
        omega
      · exact ih hmem

theorem sum_adjustTop_add_count
    (d : Nat) (hd : 1 ≤ d) (xs : List Nat) :
    (xs.map (adjustTop d)).sum + (d - 1) * topCount d xs =
      xs.sum := by
  induction xs with
  | nil => simp [topCount, adjustTop]
  | cons x xs ih =>
    by_cases hx : d ≤ x
    · have hxsum : x - d + 1 + (d - 1) = x := by omega
      simp [topCount, adjustTop, hx, List.map_cons, List.sum_cons,
        Nat.mul_add, ih, hxsum]
      omega
    · simp [topCount, adjustTop, hx, List.map_cons, List.sum_cons,
        Nat.mul_add, ih]
      omega

theorem sum_ge_topCount_mul
    (d : Nat) (xs : List Nat) :
    d * topCount d xs ≤ xs.sum := by
  induction xs with
  | nil => simp [topCount]
  | cons x xs ih =>
    by_cases hx : d ≤ x
    · simp [topCount, hx, List.sum_cons]
      nlinarith [ih]
    · simp [topCount, hx, List.sum_cons]
      nlinarith [ih, Nat.zero_le x]

theorem sum_le_length_mul_of_forall_le
    {xs : List Nat} {bound : Nat}
    (hitems : ∀ x, x ∈ xs → x ≤ bound) :
    xs.sum ≤ xs.length * bound := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := hitems x (by simp)
    have htail : ∀ y, y ∈ xs → y ≤ bound := by
      intro y hy
      exact hitems y (by simp [hy])
    have hsum := ih htail
    simp only [List.sum_cons, List.length_cons]
    nlinarith

theorem sum_ge_length_mul_of_forall_ge
    {xs : List Nat} {bound : Nat}
    (hitems : ∀ x, x ∈ xs → bound ≤ x) :
    xs.length * bound ≤ xs.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := hitems x (by simp)
    have htail : ∀ y, y ∈ xs → bound ≤ y := by
      intro y hy
      exact hitems y (by simp [hy])
    have hsum := ih htail
    simp only [List.sum_cons, List.length_cons]
    nlinarith

def liftedColor (bits : List Bool) (M u x : Nat) : Fin 3 :=
  if x ≤ M - 1 then smallColor bits x
  else if x < (u - 1) * M then symColorOfNat 2
  else smallColor bits (x - (u - 1) * M + 1)

theorem liftedColor_small_or_top
    {bits : List Bool} {M u x : Nat} {color : Fin 3}
    (hcolor : color = bitColor false ∨ color = bitColor true)
    (hvalue : liftedColor bits M u x = color) :
    x ≤ M - 1 ∨ (u - 1) * M ≤ x := by
  by_cases hbottom : x ≤ M - 1
  · exact Or.inl hbottom
  · by_cases htop : (u - 1) * M ≤ x
    · exact Or.inr htop
    · have hmid : liftedColor bits M u x = symColorOfNat 2 := by
        simp [liftedColor, hbottom, htop]
      have hne : color ≠ symColorOfNat 2 := by
        rcases hcolor with h | h
        · rw [h]
          exact bitColor_ne_two false
        · rw [h]
          exact bitColor_ne_two true
      exact False.elim (hne (hvalue.symm.trans hmid))

theorem liftedColor_two_between
    {bits : List Bool} {M u x : Nat}
    (hvalue : liftedColor bits M u x = symColorOfNat 2) :
    M ≤ x ∧ x < (u - 1) * M := by
  by_cases hbottom : x ≤ M - 1
  · have hsmall : liftedColor bits M u x = smallColor bits x := by
      simp [liftedColor, hbottom]
    have hne : smallColor bits x ≠ symColorOfNat 2 := by
      unfold smallColor
      exact bitColor_ne_two _
    exact False.elim (hne (hsmall.symm.trans hvalue))
  · by_cases htop : (u - 1) * M ≤ x
    · have hsmall :
          liftedColor bits M u x =
            smallColor bits (x - (u - 1) * M + 1) := by
        simp [liftedColor, hbottom, htop]
      have hne :
          smallColor bits (x - (u - 1) * M + 1) ≠
            symColorOfNat 2 := by
        unfold smallColor
        exact bitColor_ne_two _
      exact False.elim (hne (hsmall.symm.trans hvalue))
    · exact ⟨by omega, by omega⟩

theorem lifted_adjust_small
    {bits : List Bool} {M u x : Nat} {color : Fin 3}
    (hM : 2 ≤ M)
    (hu : 2 ≤ u)
    (hN : M * u - 2 = (u - 1) * M + (M - 2))
    (hcolor : color = bitColor false ∨ color = bitColor true)
    (hx : 1 ≤ x ∧ x ≤ M * u - 2)
    (hvalue : liftedColor bits M u x = color) :
    1 ≤ adjustTop ((u - 1) * M) x ∧
      adjustTop ((u - 1) * M) x ≤ M - 1 ∧
      smallColor bits (adjustTop ((u - 1) * M) x) = color := by
  by_cases hbottom : x ≤ M - 1
  · have hD : x < (u - 1) * M := by
      have hMd : M ≤ (u - 1) * M :=
        calc
          M = 1 * M := by simp
          _ ≤ (u - 1) * M :=
            Nat.mul_le_mul_right M (by omega : 1 ≤ u - 1)
      omega
    have hsmall : liftedColor bits M u x = smallColor bits x := by
      simp [liftedColor, hbottom]
    have hadjust : adjustTop ((u - 1) * M) x = x := by
      simp [adjustTop]
      omega
    rw [hadjust]
    exact ⟨hx.1, hbottom, by simpa [hsmall] using hvalue⟩
  · have hcase := liftedColor_small_or_top hcolor hvalue
    rcases hcase with hbottom' | htop
    · omega
    · have hshift :
          1 ≤ x - (u - 1) * M + 1 ∧
            x - (u - 1) * M + 1 ≤ M - 1 := by
        rw [hN] at hx
        omega
      have hadjust :
          adjustTop ((u - 1) * M) x =
            x - (u - 1) * M + 1 := by
        simp [adjustTop, htop]
      have hsmall :
          liftedColor bits M u x =
            smallColor bits (x - (u - 1) * M + 1) := by
        simp [liftedColor, hbottom, htop]
      rw [hadjust]
      exact ⟨hshift.1, hshift.2, by simpa [hsmall] using hvalue⟩

theorem smallMonoSol_of_adjusted
    {bits : List Bool} {M k d : Nat} {color : Fin 3}
    {xs : List Nat}
    (hlen : xs.length = k - 1)
    (hitems : ∀ x, x ∈ xs →
      1 ≤ adjustTop d x ∧ adjustTop d x ≤ M - 1 ∧
        smallColor bits (adjustTop d x) = color)
    (htarget : 1 ≤ adjustTop d xs.sum ∧
      adjustTop d xs.sum ≤ M - 1 ∧
      smallColor bits (adjustTop d xs.sum) = color)
    (hsum : (xs.map (adjustTop d)).sum = adjustTop d xs.sum) :
    MonoSol (M - 1) k (smallColor bits) color := by
  refine ⟨xs.map (adjustTop d), ?_, ?_, ?_, ?_, ?_⟩
  · simp [List.length_map, hlen]
  · intro x hx
    rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact hitems y hy
  · rw [hsum]
    exact htarget.1
  · rw [hsum]
    exact htarget.2.1
  · rw [hsum]
    exact htarget.2.2

theorem lifted_no_small_monoSol
    {bits : List Bool} {M u k : Nat} {color : Fin 3}
    (hM : 2 ≤ M) (hu : 4 ≤ u) (hk : k ≤ u)
    (hcolor : color = bitColor false ∨ color = bitColor true)
    (hnoSmall : ¬ MonoSol (M - 1) k (smallColor bits) color) :
    ¬ MonoSol (M * u - 2) k (liftedColor bits M u) color := by
  intro hsol
  rcases hsol with ⟨summands, hlen, hitems, hsumPos, hsumLe, htarget⟩
  let d := (u - 1) * M
  have hdgeM : M ≤ d := by
    have huSub : 1 ≤ u - 1 := by omega
    dsimp [d]
    calc
      M = 1 * M := by simp
      _ ≤ (u - 1) * M := Nat.mul_le_mul_right M huSub
  have hdPos : 1 ≤ d := by
    exact le_trans (by omega) hdgeM
  have hmul : d + M = M * u := by
    dsimp [d]
    calc
      (u - 1) * M + M = ((u - 1) + 1) * M := by
        rw [Nat.add_mul]
        simp
      _ = u * M := by rw [Nat.sub_add_cancel (by omega : 1 ≤ u)]
      _ = M * u := Nat.mul_comm _ _
  have hN : M * u - 2 = d + (M - 2) := by
    rw [← hmul]
    omega
  have hnotMiddle : ∀ x, x ∈ summands →
      x ≤ M - 1 ∨ d ≤ x := by
    intro x hx
    exact liftedColor_small_or_top hcolor (hitems x hx).2.2
  have hsumTop : d * topCount d summands ≤ summands.sum :=
    sum_ge_topCount_mul d summands
  have hlarge : M * u - 2 < 2 * d := by
    have hMsub : M - 2 < M := by omega
    have hdlarge : M - 2 < d := lt_of_lt_of_le hMsub hdgeM
    rw [hN]
    omega
  by_cases hzero : topCount d summands = 0
  · have hbottom : ∀ x, x ∈ summands → x ≤ M - 1 := by
      intro x hx
      rcases hnotMiddle x hx with h | h
      · exact h
      · have hpos := topCount_pos_of_mem hx h
        omega
    have hsumBound :=
      sum_le_length_mul_of_forall_le hbottom
    have hlenBound : summands.length = k - 1 := hlen
    rw [hlenBound] at hsumBound
    have hkminus : k - 1 ≤ u - 1 := by omega
    have hMsub : M - 1 < M := by omega
    have huminus : 0 < u - 1 := by omega
    have hstrict :
        (u - 1) * (M - 1) < (u - 1) * M :=
      Nat.mul_lt_mul_of_pos_left hMsub huminus
    have hle :
        (k - 1) * (M - 1) ≤ (u - 1) * (M - 1) :=
      Nat.mul_le_mul_right (M - 1) hkminus
    have hsumLt : summands.sum < d := by
      dsimp [d]
      exact lt_of_le_of_lt hsumBound (lt_of_le_of_lt hle hstrict)
    have hitemsSmall : ∀ x, x ∈ summands →
        1 ≤ adjustTop d x ∧ adjustTop d x ≤ M - 1 ∧
          smallColor bits (adjustTop d x) = color := by
      intro x hx
      have hx' : 1 ≤ x ∧ x ≤ M * u - 2 :=
        ⟨(hitems x hx).1, (hitems x hx).2.1⟩
      exact lifted_adjust_small hM (by omega) hN hcolor hx'
        (hitems x hx).2.2
    have htargetSmall :
        1 ≤ adjustTop d summands.sum ∧
          adjustTop d summands.sum ≤ M - 1 ∧
          smallColor bits (adjustTop d summands.sum) = color :=
      lifted_adjust_small hM (by omega) hN hcolor
        ⟨hsumPos, hsumLe⟩ htarget
    have htargetAdjust : adjustTop d summands.sum = summands.sum := by
      simp [adjustTop, show ¬ d ≤ summands.sum from by
        dsimp [d] at hsumLt ⊢
        exact Nat.not_le_of_gt hsumLt]
    have hsumAdjusted :
        (summands.map (adjustTop d)).sum =
          adjustTop d summands.sum := by
      have h := sum_adjustTop_add_count d hdPos summands
      rw [hzero] at h
      simp at h
      rw [htargetAdjust]
      exact h
    have hsmall :
        MonoSol (M - 1) k (smallColor bits) color :=
      smallMonoSol_of_adjusted hlen hitemsSmall htargetSmall hsumAdjusted
    exact hnoSmall hsmall
  · by_cases hone : topCount d summands = 1
    · have hsumGe : d ≤ summands.sum := by
        simpa [hone] using hsumTop
      have hitemsSmall : ∀ x, x ∈ summands →
          1 ≤ adjustTop d x ∧ adjustTop d x ≤ M - 1 ∧
            smallColor bits (adjustTop d x) = color := by
        intro x hx
        have hx' : 1 ≤ x ∧ x ≤ M * u - 2 :=
          ⟨(hitems x hx).1, (hitems x hx).2.1⟩
        exact lifted_adjust_small hM (by omega) hN hcolor hx'
          (hitems x hx).2.2
      have htargetSmall :
          1 ≤ adjustTop d summands.sum ∧
            adjustTop d summands.sum ≤ M - 1 ∧
            smallColor bits (adjustTop d summands.sum) = color :=
        lifted_adjust_small hM (by omega) hN hcolor
          ⟨hsumPos, hsumLe⟩ htarget
      have htargetAdjust :
          adjustTop d summands.sum = summands.sum - d + 1 := by
        simp [adjustTop, show d ≤ summands.sum from hsumGe]
      have hsumAdjusted :
          (summands.map (adjustTop d)).sum =
            adjustTop d summands.sum := by
        have h := sum_adjustTop_add_count d hdPos summands
        rw [hone] at h
        simp at h
        rw [htargetAdjust]
        omega
      have hsmall :
          MonoSol (M - 1) k (smallColor bits) color :=
        smallMonoSol_of_adjusted hlen hitemsSmall htargetSmall hsumAdjusted
      exact hnoSmall hsmall
    · have hgeTwo : 2 ≤ topCount d summands := by omega
      have hsumLarge : 2 * d ≤ summands.sum := by
        have hmul := hsumTop
        nlinarith
      omega

theorem lifted_no_color_two
    {bits : List Bool} {M u : Nat}
    (hM : 2 ≤ M) (hu : 4 ≤ u) :
    ¬ MonoSol (M * u - 2) u
      (liftedColor bits M u) (symColorOfNat 2) := by
  intro hsol
  rcases hsol with ⟨summands, hlen, hitems, hsumPos, hsumLe, htarget⟩
  let d := (u - 1) * M
  have hd : d = (u - 1) * M := rfl
  have hmiddle : ∀ x, x ∈ summands → M ≤ x := by
    intro x hx
    exact (liftedColor_two_between (hitems x hx).2.2).1
  have hsumLower :
      summands.length * M ≤ summands.sum :=
    sum_ge_length_mul_of_forall_ge hmiddle
  have hsumGe : d ≤ summands.sum := by
    calc
      d = summands.length * M := by
        dsimp [d]
        rw [← hlen]
      _ ≤ summands.sum := hsumLower
  have hsumLt :
      summands.sum < d :=
    (liftedColor_two_between htarget).2
  omega

theorem liftedAvoidable
    {s t M u : Nat} {bits : List Bool}
    (hs : 4 ≤ s) (hst : s ≤ t) (hu : t ≤ u)
    (hMdef : M = s * t - t - 1)
    (hsmallValid : smallColoringValid s t M bits = true) :
    Avoidable (M * u - 2) s t u := by
  have hM : 2 ≤ M := by
    have ht : 4 ≤ t := le_trans hs hst
    have hs' : 3 ≤ s - 1 := by omega
    have hprod : 12 ≤ (s - 1) * t := Nat.mul_le_mul hs' ht
    have hdist : (s - 1) * t = s * t - t := by
      simpa using (Nat.sub_mul s 1 t)
    rw [hMdef, ← hdist]
    omega
  have hU : 4 ≤ u := by omega
  have hLen : bits.length = M - 1 := by
    unfold smallColoringValid at hsmallValid
    rcases Bool.and_eq_true_iff.mp hsmallValid with ⟨hfirst, _⟩
    rcases Bool.and_eq_true_iff.mp hfirst with ⟨hlen, _⟩
    exact of_decide_eq_true hlen
  let χ := liftedColor bits M u
  have hSmall0 := smallColoring_avoids_zero hsmallValid
  have hSmall1 := smallColoring_avoids_one hsmallValid
  have hNo0 :
      ¬ MonoSol (M * u - 2) s χ (bitColor false) :=
    lifted_no_small_monoSol hM hU (by omega) (Or.inl rfl) hSmall0
  have hNo1 :
      ¬ MonoSol (M * u - 2) t χ (bitColor true) :=
    lifted_no_small_monoSol hM hU (by omega) (Or.inr rfl) hSmall1
  have hNo2 :
      ¬ MonoSol (M * u - 2) u χ (symColorOfNat 2) :=
    lifted_no_color_two hM hU
  refine ⟨χ, ?_, ?_, ?_⟩
  · simpa [bitColor, symColorOfNat] using hNo0
  · simpa [bitColor, symColorOfNat] using hNo1
  · exact hNo2

theorem construction_4_4 (u : Nat) (hu : 4 ≤ u) :
    Avoidable (11 * u - 2) 4 4 u := by
  simpa [smallColoringValid_44] using
    (liftedAvoidable (s := 4) (t := 4) (M := 11) (bits := bits44)
      (u := u) (by omega) (by omega) hu (by norm_num) smallColoringValid_44)

theorem construction_4_5 (u : Nat) (hu : 5 ≤ u) :
    Avoidable (14 * u - 2) 4 5 u := by
  simpa using
    (liftedAvoidable (s := 4) (t := 5) (M := 14) (bits := bits45)
      (u := u) (by omega) (by omega) hu (by norm_num) smallColoringValid_45)

theorem construction_4_6 (u : Nat) (hu : 6 ≤ u) :
    Avoidable (17 * u - 2) 4 6 u := by
  simpa using
    (liftedAvoidable (s := 4) (t := 6) (M := 17) (bits := bits46)
      (u := u) (by omega) (by omega) hu (by norm_num) smallColoringValid_46)

theorem construction_5_5 (u : Nat) (hu : 5 ≤ u) :
    Avoidable (19 * u - 2) 5 5 u := by
  simpa using
    (liftedAvoidable (s := 5) (t := 5) (M := 19) (bits := bits55)
      (u := u) (by omega) (by omega) hu (by norm_num) smallColoringValid_55)

end Schur
