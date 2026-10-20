import Schur.SymCNF

namespace Schur

open Std.Sat

structure VarInfo where
  kind : Nat
  color : Nat
  c : Nat
  j : Nat
  expr : Expr
  deriving DecidableEq, Repr, Inhabited

def symExprAt (s t B : Nat) (i : Nat) : Option Expr :=
  let M := symM s t
  let w := 2 * B + 1
  if i < B then
    some ⟨0, Int.ofNat (i + 1)⟩
  else
    let q := i - B
    let middle := (M - 1) * w
    if q < middle then
      let a := q / w + 1
      let b := Int.ofNat (q % w) - Int.ofNat B
      some ⟨a, b⟩
    else
      let z := q - middle
      if z < B then
        some ⟨M, Int.ofNat z - Int.ofNat B⟩
      else
        none

def inE (s t B : Nat) (e : Expr) : Bool :=
  decide
    (e.a ≤ symM s t ∧
      -Int.ofNat B ≤ e.b ∧ e.b ≤ Int.ofNat B ∧
      (e.a = 0 → 1 ≤ e.b) ∧
      (e.a = symM s t → e.b ≤ -1))

def decodeVar (s t B J : Nat) (v : Nat) : Option VarInfo :=
  let n := symExprCount s t B
  let colors := 3 * n
  let r0 := (s - 1) * n
  let r1 := (t - 1) * n
  let padding := symPaddingBase s t B
  let total := symVarCount s t B J
  if v ≥ total then
    none
  else if v < colors then
    let i := v / 3
    match symExprAt s t B i with
    | some e => some ⟨0, v % 3, 0, 0, e⟩
    | none => none
  else if v < colors + r0 then
    let q := v - colors
    match symExprAt s t B (q % n) with
    | some e => some ⟨1, 0, 0, q / n + 1, e⟩
    | none => none
  else if v < colors + r0 + r1 then
    let q := v - colors - r0
    match symExprAt s t B (q % n) with
    | some e => some ⟨1, 1, 0, q / n + 1, e⟩
    | none => none
  else if v ≥ padding then
    let q := v - padding
    let block := (J + 1) * n
    let c := q / block + 1
    let r := q % block
    match symExprAt s t B (r % n) with
    | some e => some ⟨2, 2, c, r / n, e⟩
    | none => none
  else
    none

def litIs (s t B J : Nat) (lit : Literal Nat)
    (kind color c j : Nat) (e : Expr) (positive : Bool) : Bool :=
  inE s t B e &&
    match lit with
    | (v, sign) =>
      (sign == positive) &&
        match decodeVar s t B J v with
        | some x => decide (x = ⟨kind, color, c, j, e⟩)
        | none => false

def validColorClause (s t B J : Nat) (c : CNF.Clause Nat) : Bool :=
  match c with
  | [(v0, p0), (v1, p1), (v2, p2)] =>
    if p0 && p1 && p2 then
      match decodeVar s t B J v0 with
      | some x =>
        litIs s t B J (v1, p1) 0 1 0 0 x.expr true &&
        litIs s t B J (v2, p2) 0 2 0 0 x.expr true &&
        x.kind == 0 && x.color == 0
      | none => false
    else false
  | [(v0, p0), (v1, p1)] =>
    if !p0 && !p1 then
      match decodeVar s t B J v0, decodeVar s t B J v1 with
      | some x, some y =>
        x.kind == 0 && y.kind == 0 && x.expr == y.expr &&
          inE s t B x.expr &&
          ((x.color == 0 && y.color == 1) ||
           (x.color == 0 && y.color == 2) ||
           (x.color == 1 && y.color == 2))
      | _, _ => false
    else false
  | _ => false

def validReachClause (s t B J : Nat) (c : CNF.Clause Nat) : Bool :=
  let k0 := s
  let k1 := t
  match c with
  | [(v0, p0), (v1, p1)] =>
    if !p0 && p1 then
      match decodeVar s t B J v0, decodeVar s t B J v1 with
      | some x, some y =>
          x.kind == 0 && x.color == y.color && y.kind == 1 &&
          y.j == 1 && x.expr == y.expr &&
          (x.color == 0 || x.color == 1) && inE s t B x.expr &&
          inE s t B y.expr
      | _, _ => false
    else if !p0 && !p1 then
      match decodeVar s t B J v0, decodeVar s t B J v1 with
      | some x, some y =>
          x.kind == 1 && y.kind == 0 && x.color == y.color &&
          x.expr == y.expr &&
          ((x.color == 0 && x.j == k0 - 1) ||
           (x.color == 1 && x.j == k1 - 1)) &&
          inE s t B x.expr && inE s t B y.expr
      | _, _ => false
    else false
  | [(v0, p0), (v1, p1), (v2, p2)] =>
    if !p0 && !p1 && p2 then
      match decodeVar s t B J v0, decodeVar s t B J v1,
          decodeVar s t B J v2 with
      | some x, some y, some z =>
        x.kind == 1 && y.kind == 0 && z.kind == 1 &&
          x.color == y.color && y.color == z.color &&
          x.j + 1 == z.j &&
          ((x.color == 0 && 2 ≤ z.j && z.j < k0) ||
           (x.color == 1 && 2 ≤ z.j && z.j < k1)) &&
          z.expr == symExprAdd x.expr y.expr &&
          inE s t B x.expr && inE s t B y.expr && inE s t B z.expr
      | _, _, _ => false
    else false
  | _ => false

def validPaddingClause (s t B J : Nat) (c : CNF.Clause Nat) : Bool :=
  match c with
  | [(v0, p0), (v1, p1)] =>
    if !p0 && p1 then
      match decodeVar s t B J v0, decodeVar s t B J v1 with
      | some x, some y =>
        x.kind == 0 && x.color == 2 && x.expr.a == 0 &&
          1 ≤ x.expr.b && x.expr.b ≤ Int.ofNat B &&
          y.kind == 2 &&
          y.color == 2 && y.c == x.expr.b.toNat && y.j == 0 &&
          y.expr == ⟨x.expr.b.toNat, -Int.ofNat x.expr.b.toNat⟩ &&
          1 ≤ x.expr.b.toNat && x.expr.b.toNat ≤ symM s t &&
          inE s t B x.expr && inE s t B y.expr
      | _, _ => false
    else if !p0 && !p1 then
      match decodeVar s t B J v0, decodeVar s t B J v1 with
      | some x, some y =>
        x.kind == 2 && y.kind == 0 && y.color == 2 &&
          x.color == 2 && 1 ≤ x.c && x.c ≤ symM s t &&
          x.j ≤ J && x.expr == y.expr &&
          inE s t B x.expr && inE s t B y.expr
      | _, _ => false
    else false
  | [(v0, p0), (v1, p1), (v2, p2)] =>
    if !p0 && !p1 && p2 then
      match decodeVar s t B J v0, decodeVar s t B J v1,
          decodeVar s t B J v2 with
      | some x, some y, some z =>
        x.kind == 2 && y.kind == 0 && z.kind == 2 &&
          y.color == 2 && x.color == 2 && x.c == z.c &&
          x.j + 1 == z.j && 1 ≤ z.j && z.j ≤ J &&
          z.expr == symExprReplace x.expr x.c y.expr &&
          inE s t B x.expr && inE s t B y.expr && inE s t B z.expr
      | _, _, _ => false
    else false
  | _ => false

def validClause (s t B J : Nat) (c : CNF.Clause Nat) : Bool :=
  validColorClause s t B J c ||
  validReachClause s t B J c ||
  validPaddingClause s t B J c

end Schur
