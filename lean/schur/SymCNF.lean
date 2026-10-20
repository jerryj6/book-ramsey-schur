import Std.Sat.CNF
import Std.Sat.CNF.Dimacs

namespace Schur

open Std.Sat

structure Expr where
  a : Nat
  b : Int
  deriving DecidableEq, Repr, Inhabited

def symM (s t : Nat) : Nat := s * t - t - 1

def symU0 (s t B J : Nat) : Nat := max (max (max (B + 1) (J + 1)) (max s t)) 4

def symExprs (s t B _J : Nat) : Array Expr := Id.run do
  let M := symM s t
  let mut result := #[]
  for b in [1:B + 1] do
    result := result.push ⟨0, Int.ofNat b⟩
  for a in [1:M] do
    for offset in [:2 * B + 1] do
      let b := Int.ofNat offset - Int.ofNat B
      result := result.push ⟨a, b⟩
  for offset in [:B] do
    let b := Int.ofNat offset - Int.ofNat B
    result := result.push ⟨M, b⟩
  result

def symExprIndex (s t B : Nat) (e : Expr) : Option Nat := Id.run do
  let M := symM s t
  let width := 2 * B + 1
  if e.a == 0 then
    if 0 < e.b && e.b ≤ Int.ofNat B then
      return some (e.b.toNat - 1)
    else
      return none
  if e.a < M then
    if -Int.ofNat B ≤ e.b && e.b ≤ Int.ofNat B then
      return some (B + (e.a - 1) * width + (e.b + Int.ofNat B).toNat)
    else
      return none
  if e.a == M then
    if -Int.ofNat B ≤ e.b && e.b ≤ -1 then
      return some (B + (M - 1) * width + (e.b + Int.ofNat B).toNat)
    else
      return none
  return none

def symExprCount (s t B : Nat) : Nat :=
  B + (symM s t - 1) * (2 * B + 1) + B

def symColorVar (e color : Nat) : Nat := 3 * e + color

def symReachBase (s t B : Nat) (color : Nat) : Nat :=
  3 * symExprCount s t B +
    if color = 0 then 0 else (s - 1) * symExprCount s t B

def symReachVar (s t B : Nat) (color j e : Nat) : Nat :=
  symReachBase s t B color + (j - 1) * symExprCount s t B + e

def symPaddingBase (s t B : Nat) : Nat :=
  3 * symExprCount s t B + (s - 1) * symExprCount s t B +
    (t - 1) * symExprCount s t B

def symConstantCount (s t B : Nat) : Nat := min B (symM s t)

def symPaddingVar (s t B J : Nat) (c j e : Nat) : Nat :=
  symPaddingBase s t B +
    ((c - 1) * (J + 1) + j) * symExprCount s t B + e

def symVarCount (s t B J : Nat) : Nat :=
  symPaddingBase s t B +
    symConstantCount s t B * (J + 1) * symExprCount s t B

def symExprAdd (x y : Expr) : Expr := ⟨x.a + y.a, x.b + y.b⟩

def symExprReplace (x : Expr) (c : Nat) (y : Expr) : Expr :=
  ⟨x.a + y.a, x.b - Int.ofNat c + y.b⟩

def symPositive (v : Nat) : CNF.Clause Nat := [(v, true)]
def symNegative (v : Nat) : CNF.Clause Nat := [(v, false)]

def symColorClauses (s t B J : Nat) : Array (CNF.Clause Nat) := Id.run do
  let n := (symExprs s t B J).size
  let mut clauses := #[]
  for e in [:n] do
    let c0 := symColorVar e 0
    let c1 := symColorVar e 1
    let c2 := symColorVar e 2
    clauses := clauses.push [(c0, true), (c1, true), (c2, true)]
    clauses := clauses.push [(c0, false), (c1, false)]
    clauses := clauses.push [(c0, false), (c2, false)]
    clauses := clauses.push [(c1, false), (c2, false)]
  clauses

def symReachClauses (s t B J color : Nat) : Array (CNF.Clause Nat) := Id.run do
  let es := symExprs s t B J
  let n := es.size
  let k := if color = 0 then s else t
  let mut clauses := #[]
  for e in [:n] do
    clauses := clauses.push [
      (symColorVar e color, false), (symReachVar s t B color 1 e, true)]
  for j in [2:k] do
    for x in [:n] do
      for y in [:n] do
        match symExprIndex s t B (symExprAdd es[x]! es[y]!) with
        | none => pure ()
        | some z =>
          clauses := clauses.push [
            (symReachVar s t B color (j - 1) x, false),
            (symColorVar y color, false),
            (symReachVar s t B color j z, true)]
  for e in [:n] do
    clauses := clauses.push [
      (symReachVar s t B color (k - 1) e, false),
      (symColorVar e color, false)]
  clauses

def symPaddingClauses (s t B J : Nat) : Array (CNF.Clause Nat) := Id.run do
  let es := symExprs s t B J
  let n := es.size
  let mut clauses := #[]
  for c in [1:symConstantCount s t B + 1] do
    let some start := symExprIndex s t B ⟨0, Int.ofNat c⟩
      | panic! "missing constant expression"
    let some initial := symExprIndex s t B ⟨c, -Int.ofNat c⟩
      | panic! "missing c-padding expression"
    clauses := clauses.push [
      (symColorVar start 2, false), (symPaddingVar s t B J c 0 initial, true)]
    for j in [1:J + 1] do
      for x in [:n] do
        for y in [:n] do
          match symExprIndex s t B (symExprReplace es[x]! c es[y]!) with
          | none => pure ()
          | some z =>
            clauses := clauses.push [
              (symPaddingVar s t B J c (j - 1) x, false),
              (symColorVar y 2, false),
              (symPaddingVar s t B J c j z, true)]
    for j in [0:J + 1] do
      for e in [:n] do
        clauses := clauses.push [
          (symPaddingVar s t B J c j e, false), (symColorVar e 2, false)]
  clauses

def symCNF (s t B J : Nat) : CNF Nat :=
  ⟨symColorClauses s t B J ++
    symReachClauses s t B J 0 ++
    symReachClauses s t B J 1 ++
    symPaddingClauses s t B J⟩

theorem symColorClauses_mem (s t B J : Nat) {c : CNF.Clause Nat}
    (h : c ∈ symColorClauses s t B J) : c ∈ (symCNF s t B J).clauses := by
  simp [symCNF, h]

theorem symReachColor1_mem (s t B J : Nat) {c : CNF.Clause Nat}
    (h : c ∈ symReachClauses s t B J 0) : c ∈ (symCNF s t B J).clauses := by
  simp [symCNF, h]

theorem symReachColor2_mem (s t B J : Nat) {c : CNF.Clause Nat}
    (h : c ∈ symReachClauses s t B J 1) : c ∈ (symCNF s t B J).clauses := by
  simp [symCNF, h]

theorem symPaddingClauses_mem (s t B J : Nat) {c : CNF.Clause Nat}
    (h : c ∈ symPaddingClauses s t B J) : c ∈ (symCNF s t B J).clauses := by
  simp [symCNF, h]

def symMap (s t B J : Nat) : String := Id.run do
  let es := symExprs s t B J
  let n := es.size
  let mut rows := #["var\tkind\ti\tc\tj\ta\tb"]
  for e in [:n] do
    for color in [:3] do
      let x := es[e]!
      rows := rows.push s!"{symColorVar e color + 1}\tCOL\t{color + 1}\t0\t0\t{x.a}\t{x.b}"
  for color in [:2] do
    let k := if color = 0 then s else t
    for j in [1:k] do
      for e in [:n] do
        let x := es[e]!
        rows := rows.push
          s!"{symReachVar s t B color j e + 1}\tR\t{color + 1}\t0\t{j}\t{x.a}\t{x.b}"
  for c in [1:symConstantCount s t B + 1] do
    for j in [0:J + 1] do
      for e in [:n] do
        let x := es[e]!
        rows := rows.push
          s!"{symPaddingVar s t B J c j e + 1}\tP\t3\t{c}\t{j}\t{x.a}\t{x.b}"
  return String.intercalate "\n" rows.toList ++ "\n"

end Schur
