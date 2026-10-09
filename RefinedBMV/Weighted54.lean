import RefinedBMV.FourthMoment
import Mathlib.Tactic.NoncommRing

namespace RefinedBMV
open scoped ComplexOrder MatrixOrder NNReal

/-- Positive real matrix powers, including singular PSD matrices. -/
noncomputable def positivePower {d} (A : Mat d) (r : ℝ≥0) : Mat d := CFC.nnrpow A r

theorem positivePower_nonneg {d} (A : Mat d) (r : ℝ≥0) :
    (positivePower A r).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp CFC.nnrpow_nonneg

theorem positivePower_add {d} (A : Mat d) (r s : ℝ≥0)
    (hr : 0 < r) (hs : 0 < s) :
    positivePower A r * positivePower A s = positivePower A (r+s) := by
  exact (CFC.nnrpow_add hr hs).symm

theorem sqrt_positivePower {d} (A : Mat d) (r : ℝ≥0) :
    CFC.sqrt (positivePower A r) = positivePower A (r/2) := CFC.sqrt_nnrpow

theorem sqrt_eq_positivePower {d} (A : Mat d) :
    CFC.sqrt A = positivePower A (1/2) := CFC.sqrt_eq_nnrpow A

theorem quarter_power_four {d} (A : Mat d) (hA : A.PosSemidef) :
    (positivePower A (1/4))^4 = A := by
  have h2 : positivePower A (1/4) * positivePower A (1/4) = CFC.sqrt A := by
    rw [positivePower_add A _ _ (by norm_num) (by norm_num), sqrt_eq_positivePower]
    norm_num
  calc
    (positivePower A (1/4))^4 =
        (positivePower A (1/4) * positivePower A (1/4)) *
          (positivePower A (1/4) * positivePower A (1/4)) := by noncomm_ring
    _ = CFC.sqrt A * CFC.sqrt A := by rw [h2]
    _ = A := CFC.sqrt_mul_sqrt_self A hA.nonneg

theorem sandwich_isHermitian {d} (A B : Mat d) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A * B * A).IsHermitian := by
  change (A * B * A).conjTranspose = A * B * A
  simp [Matrix.conjTranspose_mul, hA.eq, hB.eq, mul_assoc]

theorem hermitian_fourth_nonneg {d} (K : Mat d) (hK : K.IsHermitian) :
    0 ≤ reTrace (K^4) := by
  have hh := matrix_weightedSquare_nonneg (1 : Mat d) (K^2) Matrix.PosSemidef.one
  have he : (K^2).conjTranspose * 1 * K^2 = K^4 := by
    simp [hK.eq, pow_succ, mul_assoc]
  simpa only [he] using hh

/-- Move the extra positive A weight through the four sandwich copies. -/
theorem weighted_sandwich_trace {d} (A B : Mat d) (hA : A.PosSemidef) :
    reTrace ((CFC.sqrt A * B * CFC.sqrt A)^4 * A) = reTrace (A * (A * B)^4) := by
  let S := CFC.sqrt A
  have hSS : S*S = A := CFC.sqrt_mul_sqrt_self A hA.nonneg
  have he : (S*B*S)^4 = S * (B*(S*S))^3 * B * S := by noncomm_ring
  change reTrace ((S*B*S)^4 * A) = _
  rw [he]
  calc
    reTrace (S * (B*(S*S))^3 * B * S * A) =
        reTrace (S * ((B*(S*S))^3 * B * (S * A))) := by simp [mul_assoc]
    _ = reTrace (((B*(S*S))^3 * B * (S * A)) * S) := reTrace_cycle _ _
    _ = reTrace ((B*A)^3 * B * (S*A*S)) := by simp [mul_assoc, hSS]
    _ = reTrace ((B*A)^4 * A) := by
      have hsas : S*A*S = A*A := by rw [← hSS]; noncomm_ring
      rw [hsas]
      simp [pow_succ, mul_assoc]
    _ = reTrace (A * (A*B)^4) := by
      have hc : (B*A)^4 * A = ((B*A)^3 * B) * (A*A) := by simp [pow_succ, mul_assoc]
      rw [hc, reTrace_cycle]
      simp [pow_succ, mul_assoc]

/-- The full strong (5,4) chain, for PSD A and arbitrary Hermitian B. -/
theorem strong54 {d} (A B : Mat d) (hA : A.PosSemidef) (hB : B.IsHermitian) :
    reTrace (A * (A*B)^4) ≤ p 5 4 A B ∧
    reTrace ((positivePower A (5/8) * B * positivePower A (5/8))^4) ≤
      reTrace (A * (A*B)^4) ∧
    0 ≤ reTrace ((positivePower A (5/8) * B * positivePower A (5/8))^4) := by
  let J := CFC.sqrt A * B * CFC.sqrt A
  let C := positivePower A (1/4)
  have hsA : (CFC.sqrt A).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian
  have hJ : J.IsHermitian := sandwich_isHermitian _ _ hsA hB
  have hC : C.PosSemidef := positivePower_nonneg A _
  have hleft : CFC.sqrt C * J * CFC.sqrt C =
      positivePower A (5/8) * B * positivePower A (5/8) := by
    have hsum : positivePower A (1/8) * CFC.sqrt A = positivePower A (5/8) := by
      rw [sqrt_eq_positivePower, positivePower_add A _ _ (by norm_num) (by norm_num)]
      norm_num
    have hsum' : CFC.sqrt A * positivePower A (1/8) = positivePower A (5/8) := by
      rw [sqrt_eq_positivePower, positivePower_add A _ _ (by norm_num) (by norm_num)]
      norm_num
    have hsC : CFC.sqrt C = positivePower A (1/8) := by
      dsimp [C]
      rw [sqrt_positivePower]
      norm_num
    dsimp [J]
    rw [hsC]
    calc
      positivePower A (1/8) * (CFC.sqrt A * B * CFC.sqrt A) * positivePower A (1/8) =
          (positivePower A (1/8) * CFC.sqrt A) * B * (CFC.sqrt A * positivePower A (1/8)) := by
            simp [mul_assoc]
      _ = _ := by rw [hsum, hsum']
  have hc4 : C^4 = A := quarter_power_four A hA
  have hright : reTrace (J^4 * C^4) = reTrace (A * (A*B)^4) := by
    rw [hc4]
    exact weighted_sandwich_trace A B hA
  have hcomp := sandwich_fourth_le J C hJ hC
  rw [hleft, hright] at hcomp
  refine ⟨p54_ge_U A B hA hB, hcomp, ?_⟩
  exact hermitian_fourth_nonneg _ (sandwich_isHermitian _ _
    (positivePower_nonneg A _).isHermitian hB)

end RefinedBMV
