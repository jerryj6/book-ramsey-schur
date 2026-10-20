import Schur.Construction
import Schur.DirCerts
import Schur.SymCert44
import Schur.SymCert45
import Schur.SymCert46
import Schur.SymCert55
import Schur.SymSound
import Schur.SymValidCases

namespace Schur

private theorem finiteForces_4_4 (u : Nat) (hu : 4 ≤ u) (hlt : u < 21) :
    Forces (11 * u - 1) 4 4 u := by
  interval_cases u <;>
    simp [forces_4_4_u4, forces_4_4_u5, forces_4_4_u6, forces_4_4_u7,
      forces_4_4_u8, forces_4_4_u9, forces_4_4_u10, forces_4_4_u11,
      forces_4_4_u12, forces_4_4_u13, forces_4_4_u14, forces_4_4_u15,
      forces_4_4_u16, forces_4_4_u17, forces_4_4_u18, forces_4_4_u19,
      forces_4_4_u20]

private theorem finiteForces_4_5 (u : Nat) (hu : 5 ≤ u) (hlt : u < 31) :
    Forces (14 * u - 1) 4 5 u := by
  interval_cases u <;>
    simp [forces_4_5_u5, forces_4_5_u6, forces_4_5_u7, forces_4_5_u8,
      forces_4_5_u9, forces_4_5_u10, forces_4_5_u11, forces_4_5_u12,
      forces_4_5_u13, forces_4_5_u14, forces_4_5_u15, forces_4_5_u16,
      forces_4_5_u17, forces_4_5_u18, forces_4_5_u19, forces_4_5_u20,
      forces_4_5_u21, forces_4_5_u22, forces_4_5_u23, forces_4_5_u24,
      forces_4_5_u25, forces_4_5_u26, forces_4_5_u27, forces_4_5_u28,
      forces_4_5_u29, forces_4_5_u30]

private theorem finiteForces_4_6 (u : Nat) (hu : 6 ≤ u) (hlt : u < 31) :
    Forces (17 * u - 1) 4 6 u := by
  interval_cases u <;>
    simp [forces_4_6_u6, forces_4_6_u7, forces_4_6_u8, forces_4_6_u9,
      forces_4_6_u10, forces_4_6_u11, forces_4_6_u12, forces_4_6_u13,
      forces_4_6_u14, forces_4_6_u15, forces_4_6_u16, forces_4_6_u17,
      forces_4_6_u18, forces_4_6_u19, forces_4_6_u20, forces_4_6_u21,
      forces_4_6_u22, forces_4_6_u23, forces_4_6_u24, forces_4_6_u25,
      forces_4_6_u26, forces_4_6_u27, forces_4_6_u28, forces_4_6_u29,
      forces_4_6_u30]

private theorem finiteForces_5_5 (u : Nat) (hu : 5 ≤ u) (hlt : u < 31) :
    Forces (19 * u - 1) 5 5 u := by
  interval_cases u <;>
    simp [forces_5_5_u5, forces_5_5_u6, forces_5_5_u7, forces_5_5_u8,
      forces_5_5_u9, forces_5_5_u10, forces_5_5_u11, forces_5_5_u12,
      forces_5_5_u13, forces_5_5_u14, forces_5_5_u15, forces_5_5_u16,
      forces_5_5_u17, forces_5_5_u18, forces_5_5_u19, forces_5_5_u20,
      forces_5_5_u21, forces_5_5_u22, forces_5_5_u23, forces_5_5_u24,
      forces_5_5_u25, forces_5_5_u26, forces_5_5_u27, forces_5_5_u28,
      forces_5_5_u29, forces_5_5_u30]

private theorem symbolicForces_4_4 (u : Nat) (hu : 21 ≤ u) :
    Forces (11 * u - 1) 4 4 u := by
  have h := symForces_of_check_forall
    (by norm_num [symM]) valid_sym_4_4 cert_4_4 check_sym_4_4
  have hU : symU0 4 4 20 2 ≤ u := by
    simpa [symU0] using hu
  simpa [symM] using h u hU

private theorem symbolicForces_4_5 (u : Nat) (hu : 31 ≤ u) :
    Forces (14 * u - 1) 4 5 u := by
  have h := symForces_of_check_forall
    (by norm_num [symM]) valid_sym_4_5 cert_4_5 check_sym_4_5
  have hU : symU0 4 5 30 1 ≤ u := by
    simpa [symU0] using hu
  simpa [symM] using h u hU

private theorem symbolicForces_4_6 (u : Nat) (hu : 31 ≤ u) :
    Forces (17 * u - 1) 4 6 u := by
  have h := symForces_of_check_forall
    (by norm_num [symM]) valid_sym_4_6 cert_4_6 check_sym_4_6
  have hU : symU0 4 6 30 2 ≤ u := by
    simpa [symU0] using hu
  simpa [symM] using h u hU

private theorem symbolicForces_5_5 (u : Nat) (hu : 31 ≤ u) :
    Forces (19 * u - 1) 5 5 u := by
  have h := symForces_of_check_forall
    (by norm_num [symM]) valid_sym_5_5 cert_5_5 check_sym_5_5
  have hU : symU0 5 5 30 3 ≤ u := by
    simpa [symU0] using hu
  simpa [symM] using h u hU

theorem conj_4_4 : ConjFamily 4 4 := by
  intro u hu
  have hForce : Forces (11 * u - 1) 4 4 u := by
    by_cases hlt : u < 21
    · exact finiteForces_4_4 u hu hlt
    · exact symbolicForces_4_4 u (by omega)
  have hAvoid : Avoidable (11 * u - 2) 4 4 u :=
    construction_4_4 u hu
  constructor
  · simpa using hForce
  · have hSize : (11 * u - 1) - 1 = 11 * u - 2 := by omega
    simpa [SchurEq, hSize] using hAvoid

theorem conj_4_5 : ConjFamily 4 5 := by
  intro u hu
  have hForce : Forces (14 * u - 1) 4 5 u := by
    by_cases hlt : u < 31
    · exact finiteForces_4_5 u hu hlt
    · exact symbolicForces_4_5 u (by omega)
  have hAvoid : Avoidable (14 * u - 2) 4 5 u :=
    construction_4_5 u hu
  constructor
  · simpa using hForce
  · have hSize : (14 * u - 1) - 1 = 14 * u - 2 := by omega
    simpa [SchurEq, hSize] using hAvoid

theorem conj_4_6 : ConjFamily 4 6 := by
  intro u hu
  have hForce : Forces (17 * u - 1) 4 6 u := by
    by_cases hlt : u < 31
    · exact finiteForces_4_6 u hu hlt
    · exact symbolicForces_4_6 u (by omega)
  have hAvoid : Avoidable (17 * u - 2) 4 6 u :=
    construction_4_6 u hu
  constructor
  · simpa using hForce
  · have hSize : (17 * u - 1) - 1 = 17 * u - 2 := by omega
    simpa [SchurEq, hSize] using hAvoid

theorem conj_5_5 : ConjFamily 5 5 := by
  intro u hu
  have hForce : Forces (19 * u - 1) 5 5 u := by
    by_cases hlt : u < 31
    · exact finiteForces_5_5 u hu hlt
    · exact symbolicForces_5_5 u (by omega)
  have hAvoid : Avoidable (19 * u - 2) 5 5 u :=
    construction_5_5 u hu
  constructor
  · simpa using hForce
  · have hSize : (19 * u - 1) - 1 = 19 * u - 2 := by omega
    simpa [SchurEq, hSize] using hAvoid

end Schur
