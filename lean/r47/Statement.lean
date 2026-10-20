/-
Top-level statement for book Ramsey results (lead-authored; do not edit semantics).
A colouring of K_N is a symmetric predicate `red : Fin N → Fin N → Bool`.
`BookFree red m n` : every red edge has < m red common neighbours and every
blue edge has < n blue common neighbours (no red B_m, no blue B_n).
-/
def redCodeg {N : Nat} (red : Fin N → Fin N → Bool) (u v : Fin N) : Nat :=
  ((List.finRange N).filter (fun w => w ≠ u && w ≠ v && red u w && red v w)).length

def blueCodeg {N : Nat} (red : Fin N → Fin N → Bool) (u v : Fin N) : Nat :=
  ((List.finRange N).filter (fun w => w ≠ u && w ≠ v && !red u w && !red v w)).length

def Symm {N : Nat} (red : Fin N → Fin N → Bool) : Prop := ∀ u v, red u v = red v u

def BookFree {N : Nat} (red : Fin N → Fin N → Bool) (m n : Nat) : Prop :=
  ∀ u v : Fin N, u ≠ v →
    (red u v = true → redCodeg red u v < m) ∧ (red u v = false → blueCodeg red u v < n)

/-- Lower bound R(B_m,B_n) > N : an explicit good colouring of K_N. -/
def LowerBound (N m n : Nat) : Prop := ∃ red : Fin N → Fin N → Bool, Symm red ∧ BookFree red m n

/-- Upper bound R(B_m,B_n) ≤ N : no good colouring of K_N. -/
def UpperBound (N m n : Nat) : Prop := ∀ red : Fin N → Fin N → Bool, Symm red → ¬ BookFree red m n
