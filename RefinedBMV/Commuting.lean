import RefinedBMV.Exchange
import RefinedBMV.OneLetter
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic

namespace RefinedBMV
open scoped ComplexOrder MatrixOrder NNReal Matrix.Norms.L2Operator

/-- The exponential moment (1.2). Applications to the paper require A,B positive definite. -/
noncomputable def paperL {d} (n m : ℕ) (A B : Mat d) : ℝ :=
  reTrace (NormedSpace.exp (n • CFC.log A + m • CFC.log B))

theorem paperL_exchange {d} (n m : ℕ) (A B : Mat d) :
    paperL n m A B = paperL m n B A := by simp only [paperL, add_comm]

theorem paperL_commute {d} (n m : ℕ) (A B : Mat d) (hA : A.PosDef) (hB : B.PosDef)
    (hc : Commute A B) : paperL n m A B = reTrace (A^n * B^m) := by
  let : NormedAlgebra ℚ (Mat d) := NormedAlgebra.restrictScalars ℚ ℝ (Mat d)
  have hca : Commute (CFC.log A) B := hc.cfc_real Real.log
  have hcl : Commute (CFC.log A) (CFC.log B) := (hca.symm.cfc_real Real.log).symm
  have hcl' : Commute (n • CFC.log A) (m • CFC.log B) :=
    (hcl.smul_left n).smul_right m
  have hAp : IsStrictlyPositive A := hA.isUnit.isStrictlyPositive hA.posSemidef.nonneg
  have hBp : IsStrictlyPositive B := hB.isUnit.isStrictlyPositive hB.posSemidef.nonneg
  unfold paperL
  rw [NormedSpace.exp_add_of_commute hcl', NormedSpace.exp_nsmul, NormedSpace.exp_nsmul,
    CFC.exp_log A hAp, CFC.exp_log B hBp]

theorem paperT_commute {d} (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (A B : Mat d)
    (hA : A.PosSemidef) (hc : Commute A B) : paperT n m A B = reTrace (A^n * B^m) := by
  let r : ℝ≥0 := (n : ℝ≥0)/(2*m)
  let S := positivePower A r
  have hr : 0 < r := div_pos (by exact_mod_cast hn) (mul_pos (by norm_num) (by exact_mod_cast hm))
  have hcS : Commute S B := hc.cfcₙ_nnreal (NNReal.nnrpow · r)
  have hS : S.PosSemidef := positivePower_nonneg A r
  have hs2 : S^2 = positivePower A (r+r) := by
    rw [pow_two]
    exact positivePower_add A r r hr hr
  have hpower : (S^2)^m = A^n := by
    rw [← positivePower_nat _ (hS.pow 2) m hm, hs2]
    change CFC.nnrpow (CFC.nnrpow A (r+r)) (m : ℝ≥0) = A^n
    have hcomp := CFC.nnrpow_nnrpow (a := A) (x := r+r) (y := (m : ℝ≥0))
    change CFC.nnrpow (CFC.nnrpow A (r+r)) (m : ℝ≥0) =
      CFC.nnrpow A ((r+r)*(m : ℝ≥0)) at hcomp
    rw [hcomp]
    have he : (r+r)*(m : ℝ≥0) = n := by
      dsimp [r]
      have hne : (m : ℝ≥0) ≠ 0 := by exact_mod_cast hm.ne'
      field_simp
      ring
    rw [he]
    exact positivePower_nat A hA n hn
  have hsbs : S*B*S = S^2*B := by
    rw [mul_assoc, hcS.eq.symm, ← mul_assoc, pow_two]
  change reTrace ((S*B*S)^m) = _
  rw [hsbs, (hcS.pow_left 2).mul_pow, hpower]

/-- The full commuting equality (2.5), including the exponential quantity. -/
theorem paper_commuting_equalities {d} (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (A B : Mat d) (hA : A.PosDef) (hB : B.PosDef) (hc : Commute A B) :
    p n m A B = reTrace (A^n*B^m) ∧
    paperT n m A B = reTrace (A^n*B^m) ∧
    paperL n m A B = reTrace (A^n*B^m) :=
  ⟨average_commute n m A B hc, paperT_commute n m hn hm A B hA.posSemidef hc,
    paperL_commute n m A B hA hB hc⟩

end RefinedBMV
