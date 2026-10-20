import BookRamsey.RowCNF
import BookRamsey.PureBridge
import BookRamsey.Relabel
import BookRamsey.LexExists
import Std.Tactic.BVDecide.LRAT.Checker
import Mathlib.Data.Fintype.Sort
import Mathlib.Data.Fintype.Sum
import Mathlib.Logic.Equiv.Fin.Basic

namespace BookRamsey

open Std.Sat

def redNeighborhood {N : Nat} (red : Fin N → Fin N → Bool)
    (v : Fin N) : Finset (Fin N) :=
  Finset.univ.filter fun w => w ≠ v ∧ red v w = true

def redDeg {N : Nat} (red : Fin N → Fin N → Bool)
    (v : Fin N) : Nat :=
  (redNeighborhood red v).card

theorem redDeg_eq_list_count {N : Nat} (red : Fin N → Fin N → Bool)
    (v : Fin N) :
    redDeg red v =
      countTrue (((List.range N).filter fun w => w != v.val).map
        fun w => redAt red v.val w) := by
  classical
  let natPred := fun w : Nat => w != v.val && redAt red v.val w
  let finPred := fun w : Fin N => w ≠ v ∧ red v w = true
  have hpred : ∀ w : Fin N, natPred w.val = decide (finPred w) := by
    intro w
    by_cases hw : w.val = v.val
    · have heq : w = v := Fin.ext hw
      subst w
      simp [natPred, finPred, redAt]
    · have hne : (w.val != v.val) = true := by simp [hw]
      have hfin : w ≠ v := by
        intro heq
        exact hw (congrArg Fin.val heq)
      have hbit : redAt red v.val w.val = red v w := by simp [redAt]
      simp [natPred, finPred, redAt, hne, hfin, hbit]
  have hfilter :
      ((List.finRange N).filter (fun w => decide (finPred w))).map Fin.val =
        (List.range N).filter natPred := by
    calc
      ((List.finRange N).filter (fun w => decide (finPred w))).map Fin.val =
          ((List.finRange N).filter (fun w => natPred w.val)).map Fin.val := by
            congr 1
            apply List.filter_congr
            intro w hw
            exact (hpred w).symm
      _ = ((List.finRange N).map Fin.val).filter natPred := by
            symm
            exact List.filter_map
      _ = (List.range N).filter natPred := by rw [finRange_val_eq_range]
  have hlen :
      ((List.finRange N).filter (fun w => decide (finPred w))).length =
        (Finset.univ.filter finPred).card := by
    rw [← List.toFinset_card_of_nodup
      ((List.nodup_finRange N).filter _)]
    congr 1
    rw [List.toFinset_filter, List.toFinset_finRange]
    ext w
    simp [finPred]
  have hcount :
      countTrue (((List.range N).filter fun w => w != v.val).map
          fun w => redAt red v.val w) =
        ((List.range N).filter natPred).length := by
    simp [countTrue, natPred, List.filter_map, List.filter_filter,
      Bool.and_comm]
  unfold redDeg redNeighborhood
  change (Finset.univ.filter finPred).card =
    countTrue (((List.range N).filter fun w => w != v.val).map
      fun w => redAt red v.val w)
  calc
    (Finset.univ.filter finPred).card =
        ((List.finRange N).filter (fun w => decide (finPred w))).length :=
      hlen.symm
    _ = ((List.range N).filter natPred).length := by
      rw [← hfilter]
      simp
    _ = countTrue (((List.range N).filter fun w => w != v.val).map
        fun w => redAt red v.val w) := hcount.symm

theorem redDeg_relabel {N : Nat} (π : Equiv.Perm (Fin N))
    (red : Fin N → Fin N → Bool) (v : Fin N) :
    redDeg (relabel π red) v = redDeg red (π v) := by
  classical
  unfold redDeg redNeighborhood
  apply Finset.card_bij (fun w _ => π w)
  · intro w hw
    rcases Finset.mem_filter.mp hw with ⟨_, ⟨hwv, hred⟩⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change π w ≠ π v ∧ red (π v) (π w) = true
    exact ⟨fun h => hwv (π.injective h), hred⟩
  · intro w₁ hw₁ w₂ hw₂ heq
    exact π.injective heq
  · intro b hb
    refine ⟨π.symm b, ?_, ?_⟩
    · rcases Finset.mem_filter.mp hb with ⟨_, ⟨hbv, hred⟩⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      change π.symm b ≠ v ∧ red (π v) (π (π.symm b)) = true
      refine ⟨?_, ?_⟩
      · intro heq
        apply hbv
        simpa using congrArg π heq
      · simpa using hred
    · simp

def RowFixed {N : Nat} (red : Fin N → Fin N → Bool) (d : Nat) : Prop :=
  ∀ k : Nat, k < N → k ≠ 0 →
    redAt red 0 k = decide (k ≤ d)

def rowNeighborSet {N : Nat} (red : Fin N → Fin N → Bool) (v : Fin N) :
    Finset {w : Fin N // w ≠ v} :=
  Finset.univ.filter fun w => red v w.1 = true

theorem rowNonSelf_card {N : Nat} (v : Fin N) :
    Fintype.card {w : Fin N // w ≠ v} = N - 1 := by
  classical
  simpa [Fintype.card_fin] using
    (Fintype.card_subtype_compl (fun w : Fin N => w = v))

theorem rowNeighborSet_card {N : Nat} (red : Fin N → Fin N → Bool)
    (v : Fin N) {d : Nat} (hd : redDeg red v = d) :
    (rowNeighborSet red v).card = d := by
  classical
  let A := {w : Fin N // w ≠ v}
  change (Finset.univ.filter fun w : A => red v w.1 = true).card = d
  rw [← hd]
  unfold redDeg redNeighborhood
  apply Finset.card_bij (fun w _ => w.1)
  · intro w hw
    rcases Finset.mem_filter.mp hw with ⟨_, hred⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, ⟨w.2, hred⟩⟩
  · intro w₁ hw₁ w₂ hw₂ heq
    exact Subtype.ext heq
  · intro b hb
    rcases Finset.mem_filter.mp hb with ⟨_, ⟨hbv, hred⟩⟩
    refine ⟨⟨b, hbv⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hred⟩

theorem rowNeighborSet_compl_card {N : Nat} (red : Fin N → Fin N → Bool)
    (v : Fin N) {d : Nat} (hd : redDeg red v = d) :
    (rowNeighborSet red v)ᶜ.card = N - 1 - d := by
  rw [Finset.card_compl, rowNonSelf_card, rowNeighborSet_card red v hd]
  
noncomputable def rowNeighborEquiv {N : Nat} (red : Fin N → Fin N → Bool)
    (v : Fin N) {d : Nat} (hd : redDeg red v = d) :
    Fin d ⊕ Fin (N - 1 - d) ≃ {w : Fin N // w ≠ v} :=
  finSumEquivOfFinset (rowNeighborSet_card red v hd)
    (rowNeighborSet_compl_card red v hd)

theorem rowNeighborEquiv_inl_red {N : Nat} (red : Fin N → Fin N → Bool)
    (v : Fin N) {d : Nat} (hd : redDeg red v = d) (i : Fin d) :
    red v (rowNeighborEquiv red v hd (Sum.inl i)).1 = true := by
  classical
  have hmem :
      rowNeighborEquiv red v hd (Sum.inl i) ∈ rowNeighborSet red v := by
    rw [rowNeighborEquiv, finSumEquivOfFinset_inl]
    exact Finset.orderEmbOfFin_mem _ _ _
  exact (Finset.mem_filter.mp hmem).2

theorem rowNeighborEquiv_inr_not_red {N : Nat} (red : Fin N → Fin N → Bool)
    (v : Fin N) {d : Nat} (hd : redDeg red v = d) (i : Fin (N - 1 - d)) :
    red v (rowNeighborEquiv red v hd (Sum.inr i)).1 ≠ true := by
  classical
  have hmem :
      rowNeighborEquiv red v hd (Sum.inr i) ∈ (rowNeighborSet red v)ᶜ := by
    rw [rowNeighborEquiv, finSumEquivOfFinset_inr]
    exact Finset.orderEmbOfFin_mem _ _ _
  intro hred
  exact (Finset.mem_compl.mp hmem) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hred⟩)

noncomputable def rowRootEquiv {N d r : Nat} (v : Fin N)
    (e : Fin d ⊕ Fin r ≃ {w : Fin N // w ≠ v}) :
    Fin 1 ⊕ (Fin d ⊕ Fin r) ≃ Fin N := by
  let f : Fin 1 ⊕ (Fin d ⊕ Fin r) → Fin N
    | .inl _ => v
    | .inr x => (e x).1
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro x y h
    cases x with
    | inl a =>
      cases y with
      | inl b =>
        exact congrArg Sum.inl (Subsingleton.elim a b)
      | inr b =>
        exact False.elim ((e b).2 h.symm)
    | inr a =>
      cases y with
      | inl b =>
        exact False.elim ((e a).2 h)
      | inr b =>
        apply congrArg Sum.inr
        apply e.injective
        exact Subtype.ext h
  · intro w
    by_cases hw : w = v
    · refine ⟨Sum.inl 0, ?_⟩
      simp [f, hw]
    · refine ⟨Sum.inr (e.symm ⟨w, hw⟩), ?_⟩
      simp [f]

theorem rowRootEquiv_inl {N d r : Nat} (v : Fin N)
    (e : Fin d ⊕ Fin r ≃ {w : Fin N // w ≠ v}) (i : Fin 1) :
    rowRootEquiv v e (Sum.inl i) = v := rfl

theorem rowRootEquiv_inr {N d r : Nat} (v : Fin N)
    (e : Fin d ⊕ Fin r ≃ {w : Fin N // w ≠ v}) (x : Fin d ⊕ Fin r) :
    rowRootEquiv v e (Sum.inr x) = (e x).1 := rfl

theorem rowFixed_exists_of_degree {N : Nat} (red : Fin N → Fin N → Bool)
    (v : Fin N) {d : Nat} (hd : redDeg red v = d) :
    ∃ π : Equiv.Perm (Fin N), RowFixed (relabel π red) d := by
  classical
  let r := N - 1 - d
  let e := rowNeighborEquiv red v hd
  have hsize : Fintype.card (Fin d ⊕ Fin r) = N - 1 := by
    calc
      _ = Fintype.card {w : Fin N // w ≠ v} := Fintype.card_congr e
      _ = N - 1 := rowNonSelf_card v
  have hparts : d + r = N - 1 := by
    simpa [r, Fintype.card_sum] using hsize
  have hv := v.isLt
  have hNpos : 0 < N := by omega
  have hN : 1 + (N - 1) = N := by omega
  let front : Fin N ≃ Fin 1 ⊕ Fin (N - 1) :=
    (finCongr hN.symm).trans finSumFinEquiv.symm
  let tail : Fin (N - 1) ≃ Fin d ⊕ Fin r :=
    (finCongr hparts.symm).trans finSumFinEquiv.symm
  let middle : Fin N ≃ Fin 1 ⊕ (Fin d ⊕ Fin r) :=
    front.trans (Equiv.sumCongr (Equiv.refl _) tail)
  let root := rowRootEquiv v e
  let π : Equiv.Perm (Fin N) := middle.trans root
  let i0 : Fin N := ⟨0, hNpos⟩
  have hfront0 : front i0 = Sum.inl (0 : Fin 1) := by
    have hcast0 :
        finCongr hN.symm i0 = Fin.castAdd (N - 1) (0 : Fin 1) := by
      apply Fin.ext
      simp [finCongr, i0, Fin.castAdd]
    change finSumFinEquiv.symm (finCongr hN.symm i0) = Sum.inl 0
    rw [hcast0]
    simp
  have hπzero : π i0 = v := by
    calc
      π i0 = root (Sum.inl (0 : Fin 1)) := by simp [π, middle, hfront0]
      _ = v := by exact rowRootEquiv_inl v e 0
  refine ⟨π, ?_⟩
  intro k hk hk0
  let idx : Fin N := ⟨k, hk⟩
  let t : Fin (N - 1) := ⟨k - 1, by omega⟩
  have hfront : front idx = Sum.inr t := by
    have hcast : finCongr hN.symm idx = Fin.natAdd 1 t := by
      apply Fin.ext
      simp [finCongr, Fin.natAdd, idx, t]
      omega
    change finSumFinEquiv.symm (finCongr hN.symm idx) = Sum.inr t
    rw [hcast]
    simp
  simp only [redAt, dif_pos hNpos, dif_pos hk, relabel]
  change red (π i0) (π idx) = decide (k ≤ d)
  rw [hπzero]
  by_cases hkd : k ≤ d
  · let q : Fin d := ⟨k - 1, by omega⟩
    have hcast : finCongr hparts.symm t = Fin.castAdd r q := by
      apply Fin.ext
      simp [finCongr, Fin.castAdd, t, q]
    have htail : tail t = Sum.inl q := by
      change finSumFinEquiv.symm (finCongr hparts.symm t) = Sum.inl q
      rw [hcast]
      simp
    have hmiddle : middle idx = Sum.inr (Sum.inl q) := by
      simp [middle, hfront, htail]
    have hπk : π idx = (e (Sum.inl q)).1 := by
      calc
        π idx = root (Sum.inr (Sum.inl q)) := by simp [π, hmiddle]
        _ = (e (Sum.inl q)).1 := by exact rowRootEquiv_inr v e (Sum.inl q)
    rw [hπk, rowNeighborEquiv_inl_red red v hd q]
    simp [hkd]
  · let q : Fin r := ⟨k - 1 - d, by omega⟩
    have hcast : finCongr hparts.symm t = Fin.natAdd d q := by
      apply Fin.ext
      simp [finCongr, Fin.natAdd, t, q]
      omega
    have htail : tail t = Sum.inr q := by
      change finSumFinEquiv.symm (finCongr hparts.symm t) = Sum.inr q
      rw [hcast]
      simp
    have hmiddle : middle idx = Sum.inr (Sum.inr q) := by
      simp [middle, hfront, htail]
    have hπk : π idx = (e (Sum.inr q)).1 := by
      calc
        π idx = root (Sum.inr (Sum.inr q)) := by simp [π, hmiddle]
        _ = (e (Sum.inr q)).1 := by exact rowRootEquiv_inr v e (Sum.inr q)
    rw [hπk]
    have hnot := rowNeighborEquiv_inr_not_red red v hd q
    cases hval : red v (e (Sum.inr q)).1 with
    | false => simp [hval, hkd]
    | true => exact False.elim (hnot hval)

def BlockLexLeader {N : Nat} (red : Fin N → Fin N → Bool) (d : Nat) : Prop :=
  ∀ (i : Nat) (hi1 : 1 ≤ i) (hiN : i + 1 < N) (hid : i ≠ d),
    ¬ BoolLexGT
      (adjacentRow red ⟨i + 1, hiN⟩ ⟨i, by omega⟩)
      (adjacentRow red ⟨i, by omega⟩ ⟨i + 1, hiN⟩)

theorem rowDegreeAux_mem (N m n d lo hi v : Nat) (lower : Bool)
    (t j : Nat) (hv : v < N) (ht : t < N - 1)
    (hKpos : 0 < rowDegreeBound N lo hi lower)
    (hKlt : rowDegreeBound N lo hi lower < N - 1)
    (hj : j ≤ rowDegreeBound N lo hi lower) :
    RowAux.degree v lower t j ∈ rowAuxKinds N d lo hi := by
  have hKnot : ¬ (rowDegreeBound N lo hi lower = 0 ∨
      N - 1 ≤ rowDegreeBound N lo hi lower) := by omega
  simp only [rowAuxKinds, List.mem_append, List.mem_flatMap]
  apply Or.inl
  refine ⟨v, List.mem_range.mpr hv, ?_⟩
  cases lower <;>
    simp [rowDegreeRegisterKinds, hKnot, List.mem_flatMap,
      List.mem_map, List.mem_range] <;> omega

theorem rowLexAux_mem (N m n d lo hi i t : Nat)
    (hiN : i < N - 1) (hi1 : 1 ≤ i) (hid : i ≠ d)
    (ht : t < N - 3) :
    RowAux.lex i t ∈ rowAuxKinds N d lo hi := by
  unfold rowAuxKinds
  apply List.mem_append.mpr
  right
  apply List.mem_flatMap.mpr
  refine ⟨i, ?_, ?_⟩
  · apply List.mem_filter.mpr
    have hcond : (1 ≤ i && i != d) = true := by simp [hi1, hid]
    exact ⟨List.mem_range.mpr (by omega), hcond⟩
  · apply List.mem_map.mpr
    exact ⟨t, List.mem_range.mpr ht, rfl⟩

theorem rassign_rowAuxValue {N : Nat} (red : Fin N → Fin N → Bool)
    (m n d lo hi : Nat) (kind : RowAux)
    (hmem : kind ∈ rowAuxKinds N d lo hi) :
    rassign red m n d lo hi (rowAuxVar N m n d lo hi kind) =
      rowAuxValue red kind := by
  let kinds := rowAuxKinds N d lo hi
  have hidx : kinds.idxOf kind < kinds.length :=
    List.idxOf_lt_length_of_mem hmem
  have hget : (kinds.map (rowAuxValue red))[kinds.idxOf kind]'(by
        simpa using hidx) = rowAuxValue red kind := by
    simp [List.getElem_map, List.getElem_idxOf hidx]
  have hvalue : (kinds.map (rowAuxValue red)).getD
      (kinds.idxOf kind) false = rowAuxValue red kind := by
    rw [← List.getElem_eq_getD (h := by simpa using hidx) false]
    exact hget
  have hbase : rowBaseEnd N m n ≤
      rowBaseEnd N m n + kinds.idxOf kind := Nat.le_add_right _ _
  have hsub : rowBaseEnd N m n + kinds.idxOf kind -
      rowBaseEnd N m n = kinds.idxOf kind := Nat.add_sub_cancel_left _ _
  change (if rowBaseEnd N m n + (rowAuxKinds N d lo hi).idxOf kind <
      rowBaseEnd N m n then
      passign red m n (rowBaseEnd N m n + (rowAuxKinds N d lo hi).idxOf kind)
    else
      ((rowAuxKinds N d lo hi).map (rowAuxValue red)).getD
        (rowBaseEnd N m n + (rowAuxKinds N d lo hi).idxOf kind -
          rowBaseEnd N m n) false) = rowAuxValue red kind
  rw [if_neg (Nat.not_lt.mpr hbase), hsub]
  simpa [kinds] using hvalue

theorem rassign_E_symm {N : Nat} (red : Fin N → Fin N → Bool)
    (hsymm : Symm red) (m n d lo hi : Nat) {u v : Nat}
    (hu : u < N) (hv : v < N) (hne : u ≠ v) :
    rassign red m n d lo hi (E N u v) = redAt red u v := by
  have hidx : pairIdx N u v < edgeCount N := by
    by_cases huv : u < v
    · have hm := mem_pairsL_of_lt huv hv
      simpa [pairIdx, edgeCount, Nat.min_eq_left (Nat.le_of_lt huv),
        Nat.max_eq_right (Nat.le_of_lt huv)] using
        (List.idxOf_lt_length_of_mem hm)
    · have hvu : v < u := by omega
      have hm := mem_pairsL_of_lt hvu hu
      have hidx' :
          pairIdx N v u < edgeCount N := by
        simpa [pairIdx, edgeCount, Nat.min_eq_left (Nat.le_of_lt hvu),
          Nat.max_eq_right (Nat.le_of_lt hvu)] using
          (List.idxOf_lt_length_of_mem hm)
      simpa [pairIdx, Nat.min_comm, Nat.max_comm] using hidx'
  have hbase : edgeCount N ≤ rowBaseEnd N m n := by
    simp [rowBaseEnd, lexBase, blueCounterBase, redCounterBase]
    omega
  have hvar : E N u v < rowBaseEnd N m n := by
    exact Nat.lt_of_lt_of_le hidx hbase
  change (if E N u v < rowBaseEnd N m n then
      passign red m n (E N u v) else _) = redAt red u v
  rw [if_pos hvar]
  exact passign_E_symm red hsymm m n hu hv hne

theorem rassign_base_eq_passign {N m n d lo hi x : Nat}
    (red : Fin N → Fin N → Bool) (hx : x < rowBaseEnd N m n) :
    rassign red m n d lo hi x = passign red m n x := by
  simp [rassign, hx]

theorem rowTriangleVars_lt_base {N m n d lo hi i j k : Nat}
    (hij : i < j) (hjk : j < k) (hk : k < N) :
    R N i j k < rowBaseEnd N m n ∧
      B N i j k < rowBaseEnd N m n := by
  have hidx : tripleIdx N i j k < triangleCount N := by
    exact List.idxOf_lt_length_of_mem
      (mem_triplesL_of_lt hij hjk hk)
  have hbase : redCounterBase N ≤ rowBaseEnd N m n := by
    simp [rowBaseEnd, lexBase, blueCounterBase, redCounterBase]
    omega
  constructor
  · have h : R N i j k < redCounterBase N := by
      simp [R, redCounterBase]
      omega
    exact Nat.lt_of_lt_of_le h hbase
  · have h : B N i j k < redCounterBase N := by
      simp [B, redCounterBase]
      omega
    exact Nat.lt_of_lt_of_le h hbase

theorem rowTriangleClauseBundle_sat {N m n d lo hi : Nat}
    (red : Fin N → Fin N → Bool) (hsymm : Symm red)
    {i j k : Nat} (hij : i < j) (hjk : j < k) (hk : k < N) :
    (triangleClauseBundle N i j k).all
      (CNF.Clause.eval (rassign red m n d lo hi)) = true := by
  let a := rassign red m n d lo hi
  have hvars := rowTriangleVars_lt_base (N := N) (m := m) (n := n)
    (d := d) (lo := lo) (hi := hi) hij hjk hk
  have heij : a (E N i j) = redAt red i j :=
    rassign_E_symm red hsymm m n d lo hi (by omega) (by omega) (by omega)
  have heik : a (E N i k) = redAt red i k :=
    rassign_E_symm red hsymm m n d lo hi (by omega) hk (by omega)
  have hejk : a (E N j k) = redAt red j k :=
    rassign_E_symm red hsymm m n d lo hi (by omega) hk (by omega)
  have hred : a (R N i j k) =
      (a (E N i j) && a (E N i k) && a (E N j k)) := by
    calc
      a (R N i j k) = passign red m n (R N i j k) :=
        rassign_base_eq_passign red hvars.1
      _ = redTriangleAt red i j k := passign_R red m n hij hjk hk
      _ = (a (E N i j) && a (E N i k) && a (E N j k)) := by
        simp [redTriangleAt, heij, heik, hejk]
  have hblue : a (B N i j k) =
      (!a (E N i j) && !a (E N i k) && !a (E N j k)) := by
    calc
      a (B N i j k) = passign red m n (B N i j k) :=
        rassign_base_eq_passign red hvars.2
      _ = blueTriangleAt red i j k := passign_B red m n hij hjk hk
      _ = (!a (E N i j) && !a (E N i k) && !a (E N j k)) := by
        simp [blueTriangleAt, heij, heik, hejk]
  have hsat := pureTriangleTseitinClauses_sat a
    (R N i j k) (B N i j k) (E N i j) (E N i k) (E N j k)
    hred hblue
  simpa [triangleClauseBundle] using hsat

theorem rowTriangleClauses_sat {N m n d lo hi : Nat}
    (red : Fin N → Fin N → Bool) (hsymm : Symm red) :
    (triangleClauses N).all
      (CNF.Clause.eval (rassign red m n d lo hi)) = true := by
  rw [List.all_eq_true]
  intro c hc
  simp only [triangleClauses, List.mem_flatMap] at hc
  rcases hc with ⟨i, hi, hc⟩
  rcases hc with ⟨j, hj, hc⟩
  by_cases hij : i < j
  · simp only [if_pos hij, List.mem_flatMap] at hc
    rcases hc with ⟨k, hk, hc⟩
    by_cases hjk : j < k
    · simp only [if_pos hjk] at hc
      exact (List.all_eq_true.mp
        (rowTriangleClauseBundle_sat red hsymm hij hjk
          (by simpa using hk))) c hc
    · simp [hjk] at hc
  · simp [hij] at hc

theorem pairInput_lt_rowBaseEnd {N m n u v t : Nat}
    (huv : u < v) (hv : v < N) (ht : t < N - 2)
    (isRed : Bool) :
    pairInput N u v t isRed < rowBaseEnd N m n := by
  let w := pairOther N u v t
  have hw := pairOther_mem huv hv ht
  have hw_ne_u : w ≠ u := hw.2.1
  have hw_ne_v : w ≠ v := hw.2.2
  by_cases hwu : w < u
  · have htri := rowTriangleVars_lt_base (N := N) (m := m) (n := n)
      (d := 0) (lo := 0) (hi := 0) hwu huv hv
    cases isRed with
    | false => simpa [pairInput, pairTriangle, w, hwu] using htri.2
    | true => simpa [pairInput, pairTriangle, w, hwu] using htri.1
  · by_cases hwv : w < v
    · have huw : u < w := by omega
      have htri := rowTriangleVars_lt_base (N := N) (m := m) (n := n)
        (d := 0) (lo := 0) (hi := 0) huw hwv hv
      cases isRed with
      | false =>
          simpa [pairInput, pairTriangle, w, hwu, hwv] using htri.2
      | true =>
          simpa [pairInput, pairTriangle, w, hwu, hwv] using htri.1
    · have hvw : v < w := by omega
      have htri := rowTriangleVars_lt_base (N := N) (m := m) (n := n)
        (d := 0) (lo := 0) (hi := 0) huv hvw (by omega)
      cases isRed with
      | false =>
          simpa [pairInput, pairTriangle, w, hwu, hwv] using htri.2
      | true =>
          simpa [pairInput, pairTriangle, w, hwu, hwv] using htri.1

theorem S_lt_rowBaseEnd {N m n u v t l : Nat} (isRed : Bool)
    (huv : u < v) (hv : v < N) (ht : t < N - 2)
    (hl : l < counterBound m n isRed) :
    S N m n u v t l isRed < rowBaseEnd N m n := by
  have hpair : pairIdx N u v < edgeCount N := by
    have hm : (u, v) ∈ pairsL N := mem_pairsL_of_lt huv hv
    simpa [pairIdx, edgeCount, Nat.min_eq_left (Nat.le_of_lt huv),
      Nat.max_eq_right (Nat.le_of_lt huv)] using
      (List.idxOf_lt_length_of_mem hm)
  have hK : 0 < counterBound m n isRed := by omega
  have hq : pairIdx N u v * (N - 2) + t <
      edgeCount N * (N - 2) := by
    calc
      pairIdx N u v * (N - 2) + t <
          pairIdx N u v * (N - 2) + (N - 2) :=
        Nat.add_lt_add_left ht _
      _ = (pairIdx N u v + 1) * (N - 2) := by
        simp [Nat.add_mul, Nat.one_mul]
      _ ≤ edgeCount N * (N - 2) :=
        Nat.mul_le_mul_right (N - 2) (Nat.succ_le_of_lt hpair)
  have hoff :
      (pairIdx N u v * (N - 2) + t) * counterBound m n isRed + l <
        edgeCount N * (N - 2) * counterBound m n isRed := by
    calc
      _ < (pairIdx N u v * (N - 2) + t) *
            counterBound m n isRed + counterBound m n isRed :=
        Nat.add_lt_add_left hl _
      _ = (pairIdx N u v * (N - 2) + t + 1) *
            counterBound m n isRed := by
        simp [Nat.add_mul, Nat.one_mul]
      _ ≤ edgeCount N * (N - 2) * counterBound m n isRed :=
        Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hq)
  have hend : counterBase N m isRed +
      edgeCount N * (N - 2) * counterBound m n isRed ≤
        rowBaseEnd N m n := by
    cases isRed <;>
      simp [counterBase, counterBound, rowBaseEnd, lexBase,
        blueCounterBase, redCounterBase] <;> omega
  have hS : S N m n u v t l isRed <
      counterBase N m isRed +
        edgeCount N * (N - 2) * counterBound m n isRed := by
    unfold S
    simpa [Nat.add_assoc] using
      (Nat.add_lt_add_left hoff (counterBase N m isRed))
  exact Nat.lt_of_lt_of_le hS hend

theorem rassign_pairInput {N m n d lo hi : Nat}
    (red : Fin N → Fin N → Bool) (hsymm : Symm red)
    {u v t : Nat} (huv : u < v) (hv : v < N) (ht : t < N - 2)
    (isRed : Bool) :
    rassign red m n d lo hi (pairInput N u v t isRed) =
      (pairCounterInputs red u v isRed).getD t false := by
  rw [rassign_base_eq_passign red
    (pairInput_lt_rowBaseEnd huv hv ht isRed)]
  exact passign_pairInput (N := N) red hsymm m n
    (u := u) (v := v) (t := t) huv hv ht isRed

theorem rassign_S {N m n d lo hi : Nat}
    (red : Fin N → Fin N → Bool) {u v t l : Nat} (isRed : Bool)
    (huv : u < v) (hv : v < N) (ht : t < N - 2)
    (hl : l < counterBound m n isRed) :
    rassign red m n d lo hi (S N m n u v t l isRed) =
      counterRegValue red u v isRed t l := by
  rw [rassign_base_eq_passign red
    (S_lt_rowBaseEnd isRed huv hv ht hl)]
  exact passign_S red m n isRed huv hv ht hl

def rowPairInputs (N m n u v : Nat) (isRed : Bool) : List PLiteral :=
  (List.range (N - 2)).map fun t =>
    pPositive (pairInput N u v t isRed)

def rowLiteralEval (a : Nat → Bool) (lit : PLiteral) : Bool :=
  a lit.1 == lit.2

theorem rowUnitClauses_sat {N m n d lo hi : Nat}
    (red : Fin N → Fin N → Bool)
    (hsymm : Symm red)
    (hfixed : RowFixed red d) :
    (rowUnitClauses N d).all
      (CNF.Clause.eval (rassign red m n d lo hi)) = true := by
  rw [List.all_eq_true]
  intro c hc
  simp only [rowUnitClauses, List.mem_map, List.mem_range] at hc
  rcases hc with ⟨t, ht, rfl⟩
  let k := t + 1
  have hk : k < N := by dsimp [k]; omega
  have hk0 : k ≠ 0 := by dsimp [k]; omega
  have he : rassign red m n d lo hi (E N 0 k) = redAt red 0 k :=
    rassign_E_symm red hsymm m n d lo hi
      (by omega) hk (by omega)
  have hrow := hfixed k hk hk0
  by_cases hkd : k ≤ d
  · have hbit : rassign red m n d lo hi (E N 0 k) = true := by
      rw [he, hrow]
      simp [hkd]
    change CNF.Clause.eval (rassign red m n d lo hi)
      (if k ≤ d then [pPositive (E N 0 k)] else [pNegative (E N 0 k)]) = true
    simp [CNF.Clause.eval, pPositive, hbit, hkd]
  · have hbit : rassign red m n d lo hi (E N 0 k) = false := by
      rw [he, hrow]
      simp [hkd]
    change CNF.Clause.eval (rassign red m n d lo hi)
      (if k ≤ d then [pPositive (E N 0 k)] else [pNegative (E N 0 k)]) = true
    simp [CNF.Clause.eval, pNegative, hbit, hkd]

theorem rowDegreeInputs_eval {N : Nat} (red : Fin N → Fin N → Bool)
    (hsymm : Symm red) (m n d lo hi v : Nat) (hv : v < N)
    (lower : Bool) :
    (rowDegreeInputs N v lower).map (rowLiteralEval
      (rassign red m n d lo hi)) = rowDegreeBits red v lower := by
  unfold rowDegreeInputs rowDegreeBits
  cases lower <;> simp only [Bool.false_eq_true, ↓reduceIte, List.map_map]
  all_goals
    apply List.map_congr_left
    intro w hw
    rcases List.mem_filter.mp hw with ⟨hwrange, hwne⟩
    have hwN : w < N := by simpa using hwrange
    have hwne' : w ≠ v := by
      simpa [bne_iff_ne] using hwne
    have he := rassign_E_symm red hsymm m n d lo hi hv hwN (Ne.symm hwne')
    simp [rowLiteralEval, pPositive, negatePLiteral, he]

theorem countTrue_cons (b : Bool) (xs : List Bool) :
    countTrue (b :: xs) = countTrue xs + if b then 1 else 0 := by
  cases b <;> simp [countTrue]

theorem countTrue_le_length (xs : List Bool) :
    countTrue xs ≤ xs.length := by
  unfold countTrue
  exact List.length_filter_le id xs

theorem countTrue_not_map (xs : List Bool) :
    countTrue (xs.map fun b => !b) = xs.length - countTrue xs := by
  induction xs with
  | nil => simp [countTrue]
  | cons b xs ih =>
    rw [List.map_cons, countTrue_cons, countTrue_cons, ih]
    have hle := countTrue_le_length xs
    cases b <;> simp <;> omega

theorem rowOtherVertices_length {N : Nat} (v : Nat) (hv : v < N) :
    ((List.range N).filter fun w => w != v).length = N - 1 := by
  let vf : Fin N := ⟨v, hv⟩
  let finOthers := (List.finRange N).filter fun w => w ≠ vf
  have hfilter : finOthers.map Fin.val =
      (List.range N).filter fun w => w != v := by
    have hp : ∀ w : Fin N, decide (w ≠ vf) = (w.val != v) := by
      intro w
      by_cases hw : w.val = v
      · have heq : w = vf := Fin.ext hw
        rw [heq]
        simp [vf]
      · have hwne : w ≠ vf := by
          intro h
          exact hw (congrArg Fin.val h)
        have hneq : (w.val != v) = true := by simp [hw]
        simp [hwne, hneq]
    calc
      finOthers.map Fin.val =
          ((List.finRange N).filter fun w => w.val != v).map Fin.val := by
            congr 1
            apply List.filter_congr
            intro w _
            exact hp w
      _ = ((List.finRange N).map Fin.val).filter fun w => w != v := by
            symm
            exact List.filter_map
      _ = (List.range N).filter fun w => w != v := by
            rw [finRange_val_eq_range]
  have hcard : finOthers.length =
      (Finset.univ.filter fun w : Fin N => w ≠ vf).card := by
    calc
      finOthers.length = finOthers.toFinset.card := by
        symm
        exact List.toFinset_card_of_nodup
          ((List.nodup_finRange N).filter _)
      _ = (Finset.univ.filter fun w : Fin N => w ≠ vf).card := by
        congr 1
        rw [List.toFinset_filter, List.toFinset_finRange]
        ext w
        simp [vf]
  have huniv : Finset.univ.filter (fun w : Fin N => w ≠ vf) =
      Finset.univ.erase vf := by
    ext w
    simp
  calc
    ((List.range N).filter fun w => w != v).length = finOthers.length := by
      rw [← List.length_map Fin.val, hfilter]
    _ = (Finset.univ.filter fun w : Fin N => w ≠ vf).card := hcard
    _ = N - 1 := by
      rw [huniv]
      simp

theorem rowDegreeBits_red_count {N : Nat} (red : Fin N → Fin N → Bool)
    (v : Nat) (hv : v < N) :
    countTrue (rowDegreeBits red v false) = redDeg red ⟨v, hv⟩ := by
  simpa [rowDegreeBits] using (redDeg_eq_list_count red ⟨v, hv⟩).symm

theorem rowDegreeBits_lower_count {N : Nat} (red : Fin N → Fin N → Bool)
    (v : Nat) (hv : v < N) :
    countTrue (rowDegreeBits red v true) =
      N - 1 - redDeg red ⟨v, hv⟩ := by
  have hbits : rowDegreeBits red v true =
      (rowDegreeBits red v false).map fun b => !b := by
    simp [rowDegreeBits]
  rw [hbits, countTrue_not_map]
  have hlen : (rowDegreeBits red v false).length = N - 1 := by
    simp [rowDegreeBits, rowOtherVertices_length v hv]
  rw [hlen, rowDegreeBits_red_count]

theorem rowLiteralEval_negate (a : Nat → Bool) (lit : PLiteral) :
    rowLiteralEval a (negatePLiteral lit) =
      !rowLiteralEval a lit := by
  rcases lit with ⟨x, polarity⟩
  cases polarity <;> cases hx : a x <;>
    simp [rowLiteralEval, negatePLiteral, hx]

theorem rowTwoLiteral_implication_sat (a : Nat → Bool) (x : PLiteral)
    (y : Nat) (h : rowLiteralEval a x = true → a y = true) :
    ([[negatePLiteral x, pPositive y]] : List (CNF.Clause Nat)).all
      (CNF.Clause.eval a) = true := by
  rcases x with ⟨x, polarity⟩
  cases polarity <;> cases hx : a x <;> cases hy : a y <;>
    simp_all [CNF.Clause.eval, rowLiteralEval, negatePLiteral, pPositive,
      hx, hy]

theorem rowThreeLiteral_implication_sat (a : Nat → Bool) (x : PLiteral)
    (y z : Nat)
    (h : rowLiteralEval a x = true → a y = true → a z = true) :
    ([[negatePLiteral x, pNegative y, pPositive z]] :
      List (CNF.Clause Nat)).all (CNF.Clause.eval a) = true := by
  rcases x with ⟨x, polarity⟩
  cases polarity <;> cases hx : a x <;> cases hy : a y <;>
    cases hz : a z <;>
      simp_all [CNF.Clause.eval, rowLiteralEval, negatePLiteral,
        pNegative, pPositive, hx, hy, hz]

theorem rowTwoNegative_no_both_sat (a : Nat → Bool) (x : PLiteral)
    (y : Nat) (h : ¬ (rowLiteralEval a x = true ∧ a y = true)) :
    ([[negatePLiteral x, pNegative y]] : List (CNF.Clause Nat)).all
      (CNF.Clause.eval a) = true := by
  rcases x with ⟨x, polarity⟩
  cases polarity <;> cases hx : a x <;> cases hy : a y <;>
    simp_all [CNF.Clause.eval, rowLiteralEval, negatePLiteral,
      pNegative, hx, hy]

theorem rowAtMostClauses_sat (a : Nat → Bool) (inputs : List PLiteral)
    (bits : List Bool) (K : Nat) (register : Nat → Nat → Nat)
    (hvalues : inputs.map (rowLiteralEval a) = bits)
    (hbound : countTrue bits ≤ K)
    (hreg : ∀ t l, t < inputs.length → 0 < l → l ≤ K →
      a (register t l) =
        decide (l ≤ countTrue (bits.take (t + 1)))) :
    (rowAtMostClauses inputs K register).all (CNF.Clause.eval a) = true := by
  have hinput : ∀ t, t < inputs.length →
      rowLiteralEval a inputs[t]! = bits.getD t false := by
    intro t ht
    have hbit : t < bits.length := by
      rw [← hvalues]
      simp [ht]
    have hmap := congrArg (fun xs : List Bool => xs[t]?) hvalues
    simp only [List.getElem?_map] at hmap
    have hleft : (inputs[t]?) = some (inputs[t]'ht) := by simp [ht]
    have hright : (bits[t]?) = some (bits[t]'hbit) := by simp [hbit]
    rw [hleft, hright] at hmap
    have hvalue : rowLiteralEval a (inputs[t]'ht) = bits[t]'hbit :=
      Option.some.inj hmap
    have hbang : inputs[t]! = inputs[t]'ht := by simp [ht]
    calc
      rowLiteralEval a inputs[t]! = rowLiteralEval a (inputs[t]'ht) := by
        rw [hbang]
      _ = bits[t]'hbit := hvalue
      _ = bits.getD t false := List.getElem_eq_getD false
  rw [List.all_eq_true]
  intro clause hclause
  by_cases hKzero : K = 0
  · simp only [rowAtMostClauses, hKzero, ↓reduceIte,
      List.mem_map] at hclause
    rcases hclause with ⟨t, ht, rfl⟩
    have ht' : t < inputs.length := by simpa using ht
    have hinputFalse : bits.getD t false = false := by
      cases hval : bits.getD t false with
      | false => rfl
      | true =>
          have hprefix : 1 ≤ countTrue (bits.take (t + 1)) := by
            rw [countTrue_take_succ, hval]
            simp
          have hle := countTrue_take_le bits (t + 1)
          omega
    have hinput' := hinput t ht'
    change CNF.Clause.eval a [negatePLiteral inputs[t]!] = true
    have hneg : rowLiteralEval a (negatePLiteral inputs[t]!) = true := by
      rw [rowLiteralEval_negate, hinput', hinputFalse]
      rfl
    simpa [CNF.Clause.eval, rowLiteralEval] using hneg
  · have hKpos : 0 < K := Nat.pos_of_ne_zero hKzero
    simp only [rowAtMostClauses, if_neg hKzero, List.mem_flatMap] at hclause
    rcases hclause with ⟨t, ht, hclause⟩
    have ht' : t < inputs.length := List.mem_range.mp ht
    let x := inputs[t]!
    let current := fun l => register t (l + 1)
    have hbit : rowLiteralEval a x = bits.getD t false := by
      exact hinput t ht'
    have hstart : rowLiteralEval a x = true →
        a (current 0) = true := by
      intro hx
      have hi := hinput t ht'
      rw [hi] at hx
      have hreg' := hreg t 1 ht' (by omega) (by omega)
      rw [hreg']
      apply decide_eq_true_iff.mpr
      have hstep := countTrue_take_succ bits t
      rw [hstep, hx]
      simp
    by_cases htzero : t = 0
    · simp only [if_pos htzero, List.mem_singleton] at hclause
      subst clause
      simpa [x, current, pPositive] using
        (rowTwoLiteral_implication_sat a x (current 0) hstart)
    · simp only [if_neg htzero] at hclause
      let previous := fun l => register (t - 1) (l + 1)
      rcases List.mem_append.mp hclause with hprefix | hover
      · rcases List.mem_append.mp hprefix with hprefix' | hincrement
        · rcases List.mem_append.mp hprefix' with hstartMem | hpropagate
          · simp only [List.mem_singleton] at hstartMem
            subst clause
            simpa [x, current, pPositive] using
              (rowTwoLiteral_implication_sat a x (current 0) hstart)
          · rcases List.mem_map.mp hpropagate with ⟨j, hj, rfl⟩
            have hj' : j < K := by simpa using hj
            have htprev : t - 1 < inputs.length := by omega
            have hpropagateSat : a (previous j) = true →
                a (current j) = true := by
              intro hp
              have hpreg := hreg (t - 1) (j + 1) htprev (by omega) (by omega)
              have hcreg := hreg t (j + 1) ht' (by omega) (by omega)
              rw [hpreg] at hp
              rw [hcreg]
              have hmon : countTrue (bits.take t) ≤
                  countTrue (bits.take (t + 1)) := by
                rw [countTrue_take_succ]
                omega
              have hpNat : j + 1 ≤ countTrue (bits.take t) := by
                apply of_decide_eq_true
                simpa [Nat.sub_add_cancel (by omega : 1 ≤ t)] using hp
              exact decide_eq_true_iff.mpr (by omega)
            simpa [previous, current, pNegative, pPositive] using
              (twoLiteral_implication_sat a
                (previous j) (current j) hpropagateSat)
        · rcases List.mem_map.mp hincrement with ⟨j, hj, rfl⟩
          have hj' : j < K - 1 := by simpa using hj
          have htprev : t - 1 < inputs.length := by omega
          have hincrementSat : rowLiteralEval a x = true →
              a (previous j) = true →
              a (current (j + 1)) = true := by
            intro hx hp
            have hi := hinput t ht'
            rw [hi] at hx
            have hpreg := hreg (t - 1) (j + 1) htprev (by omega) (by omega)
            have hcreg := hreg t (j + 2) ht' (by omega) (by omega)
            rw [hpreg] at hp
            rw [hcreg]
            have hstep := countTrue_take_succ bits t
            have hstepNat :
                countTrue (bits.take (t + 1)) =
                  countTrue (bits.take t) + 1 := by
              rw [hstep, hx]
              rfl
            rw [hstepNat]
            have hpNat : j + 1 ≤ countTrue (bits.take t) := by
              apply of_decide_eq_true
              simpa [Nat.sub_add_cancel (by omega : 1 ≤ t)] using hp
            exact decide_eq_true_iff.mpr (by omega)
          have hsat := rowThreeLiteral_implication_sat a x
            (previous j) (current (j + 1)) hincrementSat
          have hmem :
              [negatePLiteral x, pNegative (previous j),
                pPositive (current (j + 1))] ∈
              [[negatePLiteral x, pNegative (previous j),
                pPositive (current (j + 1))]] := by simp
          change CNF.Clause.eval a
            [negatePLiteral x, pNegative (previous j),
              pPositive (current (j + 1))] = true
          exact (List.all_eq_true.mp hsat) _ hmem
      · simp only [List.mem_singleton] at hover
        subst clause
        have htprev : t - 1 < inputs.length := by omega
        have hprevK : K ≤ K := le_rfl
        have hoverSat : ¬ (rowLiteralEval a x = true ∧
            a (previous (K - 1)) = true) := by
          intro hbad
          have hbad' : rowLiteralEval a x = true ∧
              a (register (t - 1) K) = true := by
            simpa [previous, Nat.sub_add_cancel hKpos] using hbad
          have hi := hinput t ht'
          rw [hi] at hbad'
          have hpreg := hreg (t - 1) K htprev hKpos hprevK
          rw [hpreg] at hbad'
          have hpNat : K ≤ countTrue (bits.take t) := by
            have hdec : decide
                (K ≤ countTrue (bits.take ((t - 1) + 1))) = true := hbad'.2
            simpa [Nat.sub_add_cancel (by omega : 1 ≤ t)] using
              (of_decide_eq_true hdec)
          have hstep := countTrue_take_succ bits t
          have hstepNat :
              countTrue (bits.take (t + 1)) =
                countTrue (bits.take t) + 1 := by
            rw [hstep, hbad'.1]
            rfl
          have hcurrent : K + 1 ≤ countTrue (bits.take (t + 1)) := by
            rw [hstepNat]
            omega
          have hprefix := countTrue_take_le bits (t + 1)
          omega
        simpa [x, previous, pNegative] using
          (rowTwoNegative_no_both_sat a x (previous (K - 1)) hoverSat)

theorem rowSinzPairColorClauses_sat {N m n d lo hi : Nat}
    (red : Fin N → Fin N → Bool) (hsymm : Symm red)
    (hfree : BookFree red m n) {u v : Nat}
    (huv : u < v) (hv : v < N) (isRed : Bool) :
    (sinzPairColorClauses N m n u v isRed).all
      (CNF.Clause.eval (rassign red m n d lo hi)) = true := by
  let a := rassign red m n d lo hi
  let inputs := rowPairInputs N m n u v isRed
  let bits := pairCounterInputs red u v isRed
  let K := counterBound m n isRed
  let register := fun t l => S N m n u v t (l - 1) isRed
  have hlen : bits.length = N - 2 :=
    pairCounterInputs_length red huv hv isRed
  have hvalues : inputs.map (rowLiteralEval a) = bits := by
    apply List.ext_getElem
    · simp [inputs, rowPairInputs, hlen]
    · intro t htin htbits
      have ht : t < N - 2 := by simpa [inputs, rowPairInputs] using htin
      have hval := rassign_pairInput (m := m) (n := n) (d := d)
        (lo := lo) (hi := hi) red hsymm huv hv ht isRed
      have hget : bits.getD t false = bits[t] := by
        symm
        exact List.getElem_eq_getD false
      have hassign : a (pairInput N u v t isRed) = bits[t] := by
        calc
          a (pairInput N u v t isRed) = bits.getD t false := by
            simpa [a, bits] using hval
          _ = bits[t] := hget
      have htInputs : t < inputs.length := by
        simpa [inputs, rowPairInputs] using ht
      have hinput : inputs[t]'htInputs =
          pPositive (pairInput N u v t isRed) := by
        simp [inputs, rowPairInputs, ht]
      simp only [List.getElem_map]
      change rowLiteralEval a (inputs[t]'htInputs) = bits[t]
      rw [hinput]
      change (a (pairInput N u v t isRed) == true) = bits[t]
      simp [hassign]
  have hbound : countTrue bits ≤ K := by
    cases isRed with
    | false =>
        simpa [bits, K, counterBound] using
          pairCounterInputs_blue_le_of_bookFree red hsymm hfree huv
            (by omega) hv
    | true =>
        simpa [bits, K, counterBound] using
          pairCounterInputs_red_le_of_bookFree red hsymm hfree huv
            (by omega) hv
  have hreg : ∀ t l, t < inputs.length → 0 < l → l ≤ K →
      a (register t l) = decide (l ≤ countTrue (bits.take (t + 1))) := by
    intro t l ht hl hle
    have ht' : t < N - 2 := by simpa [inputs, rowPairInputs] using ht
    have hl' : l - 1 < K := by omega
    have hassign := rassign_S (m := m) (n := n) (d := d)
      (lo := lo) (hi := hi) red (u := u) (v := v) (t := t)
      (l := l - 1) isRed huv hv ht' hl'
    simpa [a, register, counterRegValue, bits,
      Nat.sub_add_cancel (by omega : 1 ≤ l)] using hassign
  have hgen : sinzPairColorClauses N m n u v isRed =
      rowAtMostClauses inputs K register := by
    by_cases hzero : K = 0
    · have hzero' : counterBound m n isRed = 0 := by
        simpa [K] using hzero
      simp only [sinzPairColorClauses, rowAtMostClauses, K,
        hzero', if_pos]
      have hlenInputs : inputs.length = N - 2 := by
        simp [inputs, rowPairInputs]
      rw [hlenInputs]
      apply List.map_congr_left
      intro t ht
      have ht' : t < N - 2 := List.mem_range.mp ht
      simp [inputs, rowPairInputs, ht', pPositive, pNegative,
        negatePLiteral]
    · have hzero' : counterBound m n isRed ≠ 0 := by
        simpa [K] using hzero
      simp only [sinzPairColorClauses, rowAtMostClauses, K,
        hzero', if_neg hzero']
      have hlenInputs : inputs.length = N - 2 := by
        simp [inputs, rowPairInputs]
      rw [hlenInputs]
      apply List.flatMap_congr
      intro t ht
      have ht' : t < N - 2 := List.mem_range.mp ht
      simp [inputs, rowPairInputs, ht', register,
        pPositive, pNegative, negatePLiteral, Nat.add_sub_cancel]
  have hsat := rowAtMostClauses_sat a inputs bits K register
    hvalues hbound hreg
  rw [hgen]
  exact hsat

theorem rowCounterClauses_sat {N m n d lo hi : Nat}
    (red : Fin N → Fin N → Bool) (hsymm : Symm red)
    (hfree : BookFree red m n) :
    (counterClauses N m n).all
      (CNF.Clause.eval (rassign red m n d lo hi)) = true := by
  rw [List.all_eq_true]
  intro c hc
  simp only [counterClauses, List.mem_flatMap] at hc
  rcases hc with ⟨u, hu, hc⟩
  rcases hc with ⟨v, hv, hc⟩
  by_cases huv : u < v
  · simp only [if_pos huv] at hc
    rcases List.mem_append.mp hc with hred | hblue
    · exact (List.all_eq_true.mp
        (rowSinzPairColorClauses_sat red hsymm hfree huv
          (by simpa using hv) true)) c hred
    · exact (List.all_eq_true.mp
        (rowSinzPairColorClauses_sat red hsymm hfree huv
          (by simpa using hv) false)) c hblue
  · simp [huv] at hc

theorem rowDegreeAtMostClauses_sat {N m n d lo hi : Nat}
    (red : Fin N → Fin N → Bool) (hsymm : Symm red)
    (v : Nat) (hv : v < N)
    (hdegree : lo ≤ redDeg red ⟨v, hv⟩ ∧
      redDeg red ⟨v, hv⟩ ≤ hi) (lower : Bool) :
    (rowDegreeAtMostClauses N m n d lo hi v lower).all
      (CNF.Clause.eval (rassign red m n d lo hi)) = true := by
  let a := rassign red m n d lo hi
  let inputs := rowDegreeInputs N v lower
  let bits := rowDegreeBits red v lower
  let K := rowDegreeBound N lo hi lower
  have hlen : inputs.length = N - 1 := by
    cases lower <;>
      simp [inputs, rowDegreeInputs, rowOtherVertices_length v hv]
  have hvalues :
      inputs.map (rowLiteralEval a) = bits := by
    simpa [a, inputs, bits] using
      rowDegreeInputs_eval red hsymm m n d lo hi v hv lower
  have hbound : countTrue bits ≤ K := by
    cases lower
    · dsimp [bits, K, rowDegreeBound]
      rw [rowDegreeBits_red_count]
      exact hdegree.2
    · dsimp [bits, K, rowDegreeBound]
      rw [rowDegreeBits_lower_count red v hv]
      omega
  have hdegmax : redDeg red ⟨v, hv⟩ ≤ N - 1 := by
    rw [← rowDegreeBits_red_count red v hv]
    calc
      countTrue (rowDegreeBits red v false) ≤
          (rowDegreeBits red v false).length := countTrue_le_length _
      _ = N - 1 := by simp [rowDegreeBits, rowOtherVertices_length v hv]
  have hnotbad : (lower && decide (N - 1 < lo)) = false := by
    cases lower
    · rfl
    · simp only [Bool.true_and]
      have hlt : ¬ N - 1 < lo := by
        exact not_lt_of_ge (le_trans hdegree.1 hdegmax)
      simp [hlt]
  by_cases hshort : N - 1 ≤ K
  · simp [rowDegreeAtMostClauses, hnotbad, K, hshort]
  · by_cases hKzero : K = 0
    · have hreg :
        ∀ t l, t < inputs.length → 0 < l → l ≤ K →
          a (rowDegreeVar N m n d lo hi v lower t l) =
            decide (l ≤ countTrue (bits.take (t + 1))) := by
        intro t l _ hl hk
        omega
      have hsat := rowAtMostClauses_sat a inputs bits K
        (rowDegreeVar N m n d lo hi v lower) hvalues hbound hreg
      have hnotzero : N - 1 ≠ 0 := by omega
      simpa [a, inputs, K, rowDegreeAtMostClauses, hnotbad, hKzero,
        hshort, hnotzero] using hsat
    · have hreg :
        ∀ t l, t < inputs.length → 0 < l → l ≤ K →
          a (rowDegreeVar N m n d lo hi v lower t l) =
            decide (l ≤ countTrue (bits.take (t + 1))) := by
        intro t l ht hl hk
        have ht' : t < N - 1 := by omega
        have hKpos : 0 < rowDegreeBound N lo hi lower := by
          dsimp [K] at *
          omega
        have hKlt : rowDegreeBound N lo hi lower < N - 1 := by
          dsimp [K] at *
          omega
        have hkind := rowDegreeAux_mem N m n d lo hi v lower t l hv ht'
          hKpos hKlt (by simpa [K] using hk)
        have hvalue := rassign_rowAuxValue red m n d lo hi
          (RowAux.degree v lower t l) hkind
        simpa [a, bits, rowDegreeVar, rowAuxValue,
          rowDegreeRegisterValue] using hvalue
      have hsat := rowAtMostClauses_sat a inputs bits K
        (rowDegreeVar N m n d lo hi v lower) hvalues hbound hreg
      simpa [a, inputs, K, rowDegreeAtMostClauses, hnotbad, hKzero,
        hshort] using hsat

theorem rowDegreeClauses_sat {N m n d lo hi : Nat}
    (red : Fin N → Fin N → Bool) (hsymm : Symm red)
    (hdegree : ∀ v : Fin N,
      lo ≤ redDeg red v ∧ redDeg red v ≤ hi) :
    (rowDegreeClauses N m n d lo hi).all
      (CNF.Clause.eval (rassign red m n d lo hi)) = true := by
  rw [List.all_eq_true]
  intro c hc
  simp only [rowDegreeClauses, List.mem_flatMap, List.mem_range] at hc
  rcases hc with ⟨v, hv, hc⟩
  rcases List.mem_append.mp hc with hupper | hlower
  · exact (List.all_eq_true.mp
      (rowDegreeAtMostClauses_sat red hsymm v hv (hdegree ⟨v, hv⟩) false))
      c hupper
  · exact (List.all_eq_true.mp
      (rowDegreeAtMostClauses_sat red hsymm v hv (hdegree ⟨v, hv⟩) true))
      c hlower

theorem rowBlockLex_no_reverse_at {N : Nat}
    (red : Fin N → Fin N → Bool) (d i t : Nat)
    (hblock : BlockLexLeader red d)
    (hi : i + 1 < N) (hi1 : 1 ≤ i) (hid : i ≠ d)
    (ht : t < N - 2)
    (hprefix : ∀ s, s < t →
      redAt red i (rowVertex i s) =
        redAt red (i + 1) (rowVertex i s))
    (hleft : redAt red i (rowVertex i t) = false)
    (hright : redAt red (i + 1) (rowVertex i t) = true) :
    False := by
  let ii : Fin N := ⟨i, by omega⟩
  let jj : Fin N := ⟨i + 1, hi⟩
  let kk : Fin N := ⟨rowVertex i t, rowVertex_lt hi ht⟩
  have hki : kk ≠ ii := by
    intro h
    apply rowVertex_ne_i i t
    simpa [kk, ii] using congrArg Fin.val h
  have hkj : kk ≠ jj := by
    intro h
    apply rowVertex_ne_i_succ i t
    simpa [kk, jj] using congrArg Fin.val h
  have hmem : kk ∈ rowVertices ii jj := by
    simp [rowVertices, ii, jj, kk, hki, hkj]
  have hsorted : (rowVertices ii jj).Pairwise (· < ·) := by
    exact (List.pairwise_lt_finRange N).filter _
  have hbefore : ∀ l ∈ rowVertices ii jj, l < kk →
      red jj l = red ii l := by
    intro l hl hlt
    have hcond : l ≠ ii ∧ l ≠ jj := by
      have := (List.mem_filter.mp hl).2
      simpa only [Bool.and_eq_true, bne_iff_ne] using this
    have hli : l.val ≠ i := by
      intro heq
      apply hcond.1
      exact Fin.ext (by simpa [ii] using heq)
    have hlj : l.val ≠ i + 1 := by
      intro heq
      apply hcond.2
      exact Fin.ext (by simpa [jj] using heq)
    have hltVal : l.val < rowVertex i t := by
      exact Fin.mk_lt_mk.mp (by simpa [kk] using hlt)
    obtain ⟨s, hst, hsl⟩ := rowVertex_before hli hlj hltVal
    have hslt : s < N - 2 := by omega
    have hvlt : rowVertex i s < N := rowVertex_lt hi hslt
    have hi0 : i < N := by omega
    have heq := hprefix s hst
    have heqFin : red ii ⟨rowVertex i s, hvlt⟩ =
        red jj ⟨rowVertex i s, hvlt⟩ := by
      simpa [redAt, ii, jj, hvlt, hi, hi0] using heq
    simpa [hsl] using heqFin.symm
  have hvalues : red jj kk = true ∧ red ii kk = false := by
    have hi0 : i < N := by omega
    have hvk : rowVertex i t < N := rowVertex_lt hi ht
    constructor
    · simpa [redAt, ii, jj, kk, hi, hvk] using hright
    · simpa [redAt, ii, jj, kk, hi0, hvk] using hleft
  have hgt := BoolLexGT.map_of_first (· < ·) (rowVertices ii jj) kk
    (fun l => red jj l) (fun l => red ii l) hsorted hmem hbefore hvalues
  exact hblock i hi1 hi hid (by
    simpa [adjacentRow, rowVertices_comm] using hgt)

theorem rowLexClauseBundle_sat {N m n d lo hi : Nat}
    (red : Fin N → Fin N → Bool) (hsymm : Symm red)
    (hblock : BlockLexLeader red d)
    {i t : Nat} (hiBound : i < N - 1) (hi1 : 1 ≤ i)
    (hid : i ≠ d) (ht : t < N - 2) :
    (rowLexClauseBundle N m n d lo hi i t).all
      (CNF.Clause.eval (rassign red m n d lo hi)) = true := by
  let a := rassign red m n d lo hi
  let k := rowVertex i t
  let x := E N i k
  let y := E N (i + 1) k
  have hiN : i + 1 < N := by omega
  have hi' : i < N := by omega
  have hk : k < N := rowVertex_lt hiN ht
  have hneI : i ≠ k := by
    intro h
    exact rowVertex_ne_i i t h.symm
  have hneJ : i + 1 ≠ k := by
    intro h
    exact rowVertex_ne_i_succ i t h.symm
  have hx : a x = redAt red i k := by
    dsimp [a, x, k]
    exact rassign_E_symm red hsymm m n d lo hi hi' hk hneI
  have hy : a y = redAt red (i + 1) k := by
    dsimp [a, y, k]
    exact rassign_E_symm red hsymm m n d lo hi hiN hk hneJ
  by_cases ht0 : t = 0
  · subst t
    have hno : ¬ (a x = false ∧ a y = true) := by
      intro hbad
      have hleft : redAt red i (rowVertex i 0) = false := by
        simpa [k] using hx.symm.trans hbad.1
      have hright : redAt red (i + 1) (rowVertex i 0) = true := by
        simpa [k] using hy.symm.trans hbad.2
      exact rowBlockLex_no_reverse_at red d i 0 hblock hiN hi1 hid
        ht (by omega) hleft hright
    have hleader : ([[pPositive x, pNegative y]] :
        List (CNF.Clause Nat)).all (CNF.Clause.eval a) = true :=
      firstLexLeaderClause_sat a x y hno
    by_cases hcur : 0 < N - 3
    · have hmem := rowLexAux_mem N m n d lo hi i 0
        hiBound hi1 hid (by omega)
      have hcurQ : a (rowLexVar N m n d lo hi i 0) =
          lexPrefixValue red i 0 := by
        have h := rassign_rowAuxValue red m n d lo hi
          (RowAux.lex i 0) hmem
        simpa [a, rowLexVar, rowAuxValue] using h
      have hq : a (rowLexVar N m n d lo hi i 0) = (a x == a y) := by
        calc
          a (rowLexVar N m n d lo hi i 0) = lexPrefixValue red i 0 := hcurQ
          _ = (redAt red i (rowVertex i 0) ==
              redAt red (i + 1) (rowVertex i 0)) :=
            lexPrefixValue_zero red i
          _ = (a x == a y) := by rw [← hx, ← hy]
      have hequality' :
          ([[pNegative x, pNegative y,
              pPositive (rowLexVar N m n d lo hi i 0)],
            [pPositive x, pPositive y,
              pPositive (rowLexVar N m n d lo hi i 0)]] :
            List (CNF.Clause Nat)).all (CNF.Clause.eval a) = true := by
        cases hax : a x <;> cases hay : a y <;>
          simp [CNF.Clause.eval, pPositive, pNegative, hq, hax, hay]
      have hlist : rowLexClauseBundle N m n d lo hi i 0 =
          [[pPositive x, pNegative y]] ++
            [[pNegative x, pNegative y,
                pPositive (rowLexVar N m n d lo hi i 0)],
              [pPositive x, pPositive y,
                pPositive (rowLexVar N m n d lo hi i 0)]] := by
        simp [rowLexClauseBundle, hcur, k, x, y]
      rw [hlist, List.all_append]
      simp [a, hleader, hequality']
    · have hlist : rowLexClauseBundle N m n d lo hi i 0 =
          [[pPositive x, pNegative y]] := by
        simp [rowLexClauseBundle, hcur, k, x, y]
      rw [hlist]
      simpa [a, CNF.Clause.eval] using hleader
  · have htpos : 0 < t := by omega
    have htprev : t - 1 < N - 3 := by omega
    let qprev := rowLexVar N m n d lo hi i (t - 1)
    have hprev : a qprev = lexPrefixValue red i (t - 1) := by
      have hmem := rowLexAux_mem N m n d lo hi i (t - 1)
        hiBound hi1 hid htprev
      have h := rassign_rowAuxValue red m n d lo hi
        (RowAux.lex i (t - 1)) hmem
      simpa [a, qprev, rowLexVar, rowAuxValue] using h
    have hprevNo : lexPrefixValue red i (t - 1) = true →
        ¬ (redAt red i k = false ∧ redAt red (i + 1) k = true) := by
      intro hp hbad
      have hprefix : ∀ s, s < t →
          redAt red i (rowVertex i s) =
            redAt red (i + 1) (rowVertex i s) := by
        intro s hst
        exact lexPrefixValue_at red (by omega) hp
      exact rowBlockLex_no_reverse_at red d i t hblock hiN hi1 hid ht
        hprefix hbad.1 hbad.2
    have hno : a qprev = true → ¬ (a x = false ∧ a y = true) := by
      intro hp hbad
      apply hprevNo
      · rw [← hprev]
        exact hp
      · exact ⟨by rw [← hx]; exact hbad.1,
          by rw [← hy]; exact hbad.2⟩
    have hleader :
        ([[pNegative qprev, pPositive x, pNegative y]] :
          List (CNF.Clause Nat)).all (CNF.Clause.eval a) = true :=
      chainedLexLeaderClause_sat a x y qprev hno
    by_cases hcur : t < N - 3
    · have hmem := rowLexAux_mem N m n d lo hi i t
        hiBound hi1 hid hcur
      have hcurQ : a (rowLexVar N m n d lo hi i t) =
          lexPrefixValue red i t := by
        have h := rassign_rowAuxValue red m n d lo hi
          (RowAux.lex i t) hmem
        simpa [a, rowLexVar, rowAuxValue] using h
      have hrec : lexPrefixValue red i t =
          (lexPrefixValue red i (t - 1) &&
            (redAt red i k == redAt red (i + 1) k)) := by
        have h := lexPrefixValue_succ red i (t - 1)
        simpa [k, Nat.sub_add_cancel (by omega : 1 ≤ t)] using h
      have hq : a (rowLexVar N m n d lo hi i t) =
          (a qprev && (a x == a y)) := by
        calc
          a (rowLexVar N m n d lo hi i t) = lexPrefixValue red i t := hcurQ
          _ = (lexPrefixValue red i (t - 1) &&
              (redAt red i k == redAt red (i + 1) k)) := hrec
          _ = (a qprev && (a x == a y)) := by rw [← hprev, ← hx, ← hy]
      have hequality' :
          ([[pNegative qprev, pNegative x, pNegative y,
              pPositive (rowLexVar N m n d lo hi i t)],
            [pNegative qprev, pPositive x, pPositive y,
              pPositive (rowLexVar N m n d lo hi i t)]] :
            List (CNF.Clause Nat)).all (CNF.Clause.eval a) = true := by
        cases hp : a qprev <;> cases hax : a x <;> cases hay : a y <;>
          simp [CNF.Clause.eval, pPositive, pNegative, hq, hp, hax, hay]
      have hlist :
          rowLexClauseBundle N m n d lo hi i t =
            [[pNegative qprev, pPositive x, pNegative y]] ++
              [[pNegative qprev, pNegative x, pNegative y,
                  pPositive (rowLexVar N m n d lo hi i t)],
                [pNegative qprev, pPositive x, pPositive y,
                  pPositive (rowLexVar N m n d lo hi i t)]] := by
        simp [rowLexClauseBundle, ht0, hcur, qprev, k, x, y]
      rw [hlist, List.all_append]
      simp [a, hleader, hequality']
    · have hlist : rowLexClauseBundle N m n d lo hi i t =
          [[pNegative qprev, pPositive x, pNegative y]] := by
        simp [rowLexClauseBundle, ht0, hcur, qprev, k, x, y]
      rw [hlist]
      simpa [a, CNF.Clause.eval] using hleader

theorem rowBlockLexClauses_sat {N m n d lo hi : Nat}
    (red : Fin N → Fin N → Bool) (hsymm : Symm red)
    (hblock : BlockLexLeader red d) :
    (rowBlockLexClauses N m n d lo hi).all
      (CNF.Clause.eval (rassign red m n d lo hi)) = true := by
  rw [List.all_eq_true]
  intro c hc
  simp only [rowBlockLexClauses, List.mem_flatMap] at hc
  rcases hc with ⟨i, hi, hc⟩
  rcases hc with ⟨t, ht, hc⟩
  rcases List.mem_filter.mp hi with ⟨hiRange, hiCond⟩
  have hiBound : i < N - 1 := by simpa using hiRange
  have hcond : 1 ≤ i ∧ i ≠ d := by
    simpa only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne] using hiCond
  have hi1 := hcond.1
  have hid := hcond.2
  have ht' : t < N - 2 := by simpa using ht
  exact (List.all_eq_true.mp
    (rowLexClauseBundle_sat red hsymm hblock hiBound hi1 hid ht')) c hc

theorem rcnf_sat {N m n d lo hi : Nat}
    (red : Fin N → Fin N → Bool) (hsymm : Symm red)
    (hfree : BookFree red m n) (hfixed : RowFixed red d)
    (hdegree : ∀ v : Fin N,
      lo ≤ redDeg red v ∧ redDeg red v ≤ hi)
    (hblock : BlockLexLeader red d) :
    (rcnf N m n d lo hi).eval (rassign red m n d lo hi) = true := by
  simp [rcnf, CNF.eval, List.all_append, rowTriangleClauses_sat,
    rowCounterClauses_sat, rowUnitClauses_sat, rowDegreeClauses_sat,
    rowBlockLexClauses_sat, hsymm, hfree, hfixed, hdegree, hblock]

theorem rowFixed_swap {N : Nat} (red : Fin N → Fin N → Bool)
    (d i : Nat) (hfixed : RowFixed red d)
    (hi1 : 1 ≤ i) (hiN : i + 1 < N) (hid : i ≠ d) :
    RowFixed (relabel
      (Equiv.swap ⟨i, by omega⟩ ⟨i + 1, hiN⟩) red) d := by
  let ii : Fin N := ⟨i, by omega⟩
  let jj : Fin N := ⟨i + 1, hiN⟩
  let zero : Fin N := ⟨0, by omega⟩
  let σ := Equiv.swap ii jj
  have hzero : σ zero = zero := by
    apply Equiv.swap_apply_of_ne_of_ne
    · intro h
      have := congrArg Fin.val h
      dsimp [zero, ii] at this
      omega
    · intro h
      have := congrArg Fin.val h
      dsimp [zero, jj] at this
      omega
  have hsame : decide (i ≤ d) = decide (i + 1 ≤ d) := by
    by_cases h₁ : i ≤ d <;> by_cases h₂ : i + 1 ≤ d <;>
      simp_all <;> omega
  intro k hk hk0
  let z : Fin N := ⟨k, hk⟩
  have hN0 : 0 < N := by omega
  simp only [redAt, dif_pos hN0, dif_pos hk, relabel]
  change red (σ zero) (σ z) = decide (k ≤ d)
  rw [hzero]
  by_cases hzi : z = ii
  · have hik : k = i := congrArg Fin.val hzi
    have hσz : σ z = jj := by
      rw [hzi]
      simp [σ]
    have hiFixed := hfixed i (by omega) (by omega)
    have hjFixed := hfixed (i + 1) (by omega) (by omega)
    have hiLt : i < N := by omega
    have hiRed : red zero ii = decide (i ≤ d) := by
      simpa [redAt, zero, ii, hN0, hiLt] using hiFixed
    have hjRed : red zero jj = decide (i + 1 ≤ d) := by
      simpa [redAt, zero, jj, hN0, hiN] using hjFixed
    rw [hσz]
    rw [hjRed]
    simpa [hik] using hsame.symm
  · by_cases hzj : z = jj
    · have hik : k = i + 1 := congrArg Fin.val hzj
      have hσz : σ z = ii := by
        rw [hzj]
        simp [σ]
      have hiFixed := hfixed i (by omega) (by omega)
      have hjFixed := hfixed (i + 1) (by omega) (by omega)
      have hiLt : i < N := by omega
      have hiRed : red zero ii = decide (i ≤ d) := by
        simpa [redAt, zero, ii, hN0, hiLt] using hiFixed
      have hjRed : red zero jj = decide (i + 1 ≤ d) := by
        simpa [redAt, zero, jj, hN0, hiN] using hjFixed
      rw [hσz]
      rw [hiRed]
      simpa [hik] using hsame
    · have hfix := Equiv.swap_apply_of_ne_of_ne hzi hzj
      rw [hfix]
      simpa [redAt, zero, z, hN0, hk] using hfixed k hk hk0

theorem blockLex_exists_of_rowFixed {N m n d : Nat}
    (red : Fin N → Fin N → Bool) (hsymm : Symm red)
    (hfree : BookFree red m n)
    (hrow : ∃ π : Equiv.Perm (Fin N), RowFixed (relabel π red) d) :
    ∃ π : Equiv.Perm (Fin N),
      RowFixed (relabel π red) d ∧
      Symm (relabel π red) ∧ BookFree (relabel π red) m n ∧
      BlockLexLeader (relabel π red) d := by
  classical
  rcases hrow with ⟨π₀, hπ₀⟩
  let candidates := (Finset.univ : Finset (Equiv.Perm (Fin N))).filter
    fun π => RowFixed (relabel π red) d
  have hπ₀' : π₀ ∈ candidates := Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, hπ₀⟩
  obtain ⟨π, hπ, hmax⟩ :=
    Finset.exists_max_image candidates
      (fun σ => rank (relabel σ red)) ⟨π₀, hπ₀'⟩
  let red' := relabel π red
  refine ⟨π, ?_, symm_relabel π red hsymm,
    bookFree_relabel π red hfree, ?_⟩
  · exact (Finset.mem_filter.mp hπ).2
  intro i hi1 hiN hid
  let ii : Fin N := ⟨i, by omega⟩
  let jj : Fin N := ⟨i + 1, hiN⟩
  let σ := Equiv.swap ii jj
  intro hgt
  have hswapRow : RowFixed (relabel σ red') d :=
    rowFixed_swap red' d i (Finset.mem_filter.mp hπ).2 hi1 hiN hid
  have hcomp : relabel (σ.trans π) red = relabel σ red' := by
    funext u v
    simp [relabel, red', Equiv.trans_apply]
  have hπswap : σ.trans π ∈ candidates := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hcomp]
    exact hswapRow
  have hmax' := hmax (σ.trans π) hπswap
  rw [hcomp] at hmax'
  have hinc := swap_rank_gt red' (symm_relabel π red hsymm)
    ii hiN hgt
  exact (Nat.not_lt_of_ge hmax') hinc

theorem row_excl_of_unsat {N m n d lo hi : Nat}
    (hunsat : (rcnf N m n d lo hi).Unsat) :
    ∀ red : Fin N → Fin N → Bool, Symm red → BookFree red m n →
      (∀ w : Fin N, lo ≤ redDeg red w ∧ redDeg red w ≤ hi) →
      ∀ v : Fin N, redDeg red v ≠ d := by
  intro red hsymm hfree hdegree v hd
  obtain ⟨π₀, hrow₀⟩ := rowFixed_exists_of_degree red v hd
  obtain ⟨π, hrow, hsymm', hfree', hblock⟩ :=
    blockLex_exists_of_rowFixed red hsymm hfree ⟨π₀, hrow₀⟩
  let red' := relabel π red
  have hdegree' : ∀ w : Fin N, lo ≤ redDeg red' w ∧ redDeg red' w ≤ hi := by
    intro w
    dsimp [red']
    rw [redDeg_relabel]
    exact hdegree (π w)
  have hsat := rcnf_sat red' hsymm' hfree' hrow hdegree' hblock
  have hfalse := hunsat (rassign red' m n d lo hi)
  rw [hsat] at hfalse
  cases hfalse

theorem row_excl_of_check {N m n d lo hi : Nat}
    (cert : Array Std.Tactic.BVDecide.LRAT.IntAction)
    (hcheck :
      Std.Tactic.BVDecide.LRAT.check cert (rcnf N m n d lo hi) = true) :
    ∀ red : Fin N → Fin N → Bool, Symm red → BookFree red m n →
      (∀ w : Fin N, lo ≤ redDeg red w ∧ redDeg red w ≤ hi) →
      ∀ v : Fin N, redDeg red v ≠ d := by
  apply row_excl_of_unsat
  exact Std.Tactic.BVDecide.LRAT.check_sound cert
    (rcnf N m n d lo hi) hcheck

end BookRamsey
