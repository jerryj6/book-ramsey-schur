/-
  Trusted statement file for the generalized Schur number results.
  S(3; s,t,u) = least N such that every 3-colouring of [1,N] has a colour-0
  solution of x_1+...+x_{s-1} = x_s, or a colour-1 solution for t, or a
  colour-2 solution for u (repetition allowed).
  Ahmed–Schaal Conjecture 2: S(3;s,t,u) = s*t*u - t*u - u - 1 for 4 ≤ s ≤ t ≤ u.
  DO NOT MODIFY after review.
-/
namespace Schur

/-- `χ` has a monochromatic colour-`i` solution of `L(k)` inside `[1,N]`. -/
def MonoSol (N k : Nat) (χ : Nat → Fin 3) (i : Fin 3) : Prop :=
  ∃ l : List Nat, l.length = k - 1 ∧
    (∀ x ∈ l, 1 ≤ x ∧ x ≤ N ∧ χ x = i) ∧
    1 ≤ l.sum ∧ l.sum ≤ N ∧ χ l.sum = i

/-- Every 3-colouring of `[1,N]` contains a forced monochromatic solution. -/
def Forces (N s t u : Nat) : Prop :=
  ∀ χ : Nat → Fin 3, MonoSol N s χ 0 ∨ MonoSol N t χ 1 ∨ MonoSol N u χ 2

/-- Some 3-colouring of `[1,N]` avoids all three. -/
def Avoidable (N s t u : Nat) : Prop :=
  ∃ χ : Nat → Fin 3, ¬ MonoSol N s χ 0 ∧ ¬ MonoSol N t χ 1 ∧ ¬ MonoSol N u χ 2

/-- `S(3;s,t,u) = N`. -/
def SchurEq (N s t u : Nat) : Prop := Forces N s t u ∧ Avoidable (N - 1) s t u

/-- Target shape (per fixed pair (s,t)): for all u ≥ t,
    `SchurEq ((s*t - t - 1) * u - 1) s t u`. -/
def ConjFamily (s t : Nat) : Prop :=
  ∀ u, t ≤ u → SchurEq ((s * t - t - 1) * u - 1) s t u

end Schur
