import BookRamsey.PureCNF

namespace BookRamsey

open Std.Sat

inductive RowAux where
  | degree (v : Nat) (lower : Bool) (t j : Nat)
  | lex (i t : Nat)
deriving DecidableEq

def rowBaseEnd (N m n : Nat) : Nat := lexBase N m n

def rowDegreeBound (N lo hi : Nat) (lower : Bool) : Nat :=
  if lower then N - 1 - lo else hi

def rowDegreeRegisterKinds (N v : Nat) (lower : Bool) (K : Nat) :
    List RowAux :=
  if K = 0 || N - 1 ≤ K then []
  else
    (List.range (N - 1)).flatMap fun t =>
      (List.range (K + 1)).map fun j => .degree v lower t j

def rowAuxKinds (N d lo hi : Nat) : List RowAux :=
  ((List.range N).flatMap fun v =>
    rowDegreeRegisterKinds N v false (rowDegreeBound N lo hi false) ++
      rowDegreeRegisterKinds N v true (rowDegreeBound N lo hi true)) ++
    (((List.range (N - 1)).filter fun i => 1 ≤ i && i != d).flatMap
      fun i => (List.range (N - 3)).map fun t => .lex i t)

def rowAuxVar (N m n d lo hi : Nat) (kind : RowAux) : Nat :=
  rowBaseEnd N m n + (rowAuxKinds N d lo hi).idxOf kind

def rowDegreeVar (N m n d lo hi v : Nat) (lower : Bool) (t j : Nat) :
    Nat :=
  rowAuxVar N m n d lo hi (.degree v lower t j)

def rowLexVar (N m n d lo hi i t : Nat) : Nat :=
  rowAuxVar N m n d lo hi (.lex i t)

def negatePLiteral (lit : PLiteral) : PLiteral := (lit.1, !lit.2)

def rowAtMostClauses (xs : List PLiteral) (K : Nat)
    (register : Nat → Nat → Nat) : List (CNF.Clause Nat) :=
  if K = 0 then
    (List.range xs.length).map fun t =>
      [negatePLiteral xs[t]!]
  else
    (List.range xs.length).flatMap fun t =>
      let x := xs[t]!
      let current l := register t (l + 1)
      let start := [[negatePLiteral x, pPositive (current 0)]]
      if t = 0 then
        start
      else
        let previous l := register (t - 1) (l + 1)
        let propagate := (List.range K).map fun j =>
          [pNegative (previous j), pPositive (current j)]
        let increment := (List.range (K - 1)).map fun j =>
          [negatePLiteral x, pNegative (previous j),
            pPositive (current (j + 1))]
        let overflow :=
          [[negatePLiteral x, pNegative (previous (K - 1))]]
        start ++ propagate ++ increment ++ overflow

def rowDegreeInputs (N v : Nat) (lower : Bool) : List PLiteral :=
  let inputs := ((List.range N).filter fun w => w != v).map
    fun w => pPositive (E N v w)
  if lower then inputs.map negatePLiteral else inputs

def rowDegreeAtMostClauses (N m n d lo hi v : Nat) (lower : Bool) :
    List (CNF.Clause Nat) :=
  if lower && N - 1 < lo then
    [[]]
  else
    let K := rowDegreeBound N lo hi lower
    if N - 1 ≤ K then
      []
    else
      rowAtMostClauses (rowDegreeInputs N v lower) K
        (rowDegreeVar N m n d lo hi v lower)

def rowDegreeClauses (N m n d lo hi : Nat) :
    List (CNF.Clause Nat) :=
  (List.range N).flatMap fun v =>
    rowDegreeAtMostClauses N m n d lo hi v false ++
      rowDegreeAtMostClauses N m n d lo hi v true

def rowUnitClauses (N d : Nat) : List (CNF.Clause Nat) :=
  (List.range (N - 1)).map fun t =>
    let k := t + 1
    if k ≤ d then [pPositive (E N 0 k)] else [pNegative (E N 0 k)]

def rowLexClauseBundle (N m n d lo hi i t : Nat) :
    List (CNF.Clause Nat) :=
  let k := rowVertex i t
  let a := E N i k
  let b := E N (i + 1) k
  let leader :=
    if t = 0 then
      [[pPositive a, pNegative b]]
    else
      [[pNegative (rowLexVar N m n d lo hi i (t - 1)),
        pPositive a, pNegative b]]
  if t < N - 3 then
    let q := rowLexVar N m n d lo hi i t
    let equality :=
      if t = 0 then
        [[pNegative a, pNegative b, pPositive q],
          [pPositive a, pPositive b, pPositive q]]
      else
        let previous := rowLexVar N m n d lo hi i (t - 1)
        [[pNegative previous, pNegative a, pNegative b, pPositive q],
          [pNegative previous, pPositive a, pPositive b, pPositive q]]
    leader ++ equality
  else
    leader

def rowBlockLexClauses (N m n d lo hi : Nat) :
    List (CNF.Clause Nat) :=
  (((List.range (N - 1)).filter fun i => 1 ≤ i && i != d).flatMap
    fun i => (List.range (N - 2)).flatMap fun t =>
      rowLexClauseBundle N m n d lo hi i t)

def rcnf (N m n d lo hi : Nat) : CNF Nat :=
  { clauses := (triangleClauses N ++ counterClauses N m n ++
      rowUnitClauses N d ++ rowDegreeClauses N m n d lo hi ++
      rowBlockLexClauses N m n d lo hi).toArray }

def rowDegreeBits {N : Nat} (red : Fin N → Fin N → Bool) (v : Nat)
    (lower : Bool) : List Bool :=
  ((List.range N).filter fun w => w != v).map fun w =>
    let bit := redAt red v w
    if lower then !bit else bit

def rowDegreeRegisterValue {N : Nat} (red : Fin N → Fin N → Bool)
    (v : Nat) (lower : Bool) (t j : Nat) : Bool :=
  decide (j ≤ countTrue ((rowDegreeBits red v lower).take (t + 1)))

def rowAuxValue {N : Nat} (red : Fin N → Fin N → Bool)
    (kind : RowAux) : Bool :=
  match kind with
  | .degree v lower t j => rowDegreeRegisterValue red v lower t j
  | .lex i t => lexPrefixValue red i t

def rassign {N : Nat} (red : Fin N → Fin N → Bool)
    (m n d lo hi x : Nat) : Bool :=
  let base := rowBaseEnd N m n
  if x < base then
    passign red m n x
  else
    ((rowAuxKinds N d lo hi).map (rowAuxValue red)).getD (x - base) false

end BookRamsey
