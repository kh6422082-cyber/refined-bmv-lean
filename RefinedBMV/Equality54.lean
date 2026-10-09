import RefinedBMV.Weighted54
import Mathlib.Analysis.CStarAlgebra.Fuglede
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Tactic.Module

namespace RefinedBMV
open scoped ComplexOrder MatrixOrder
open scoped Matrix.Norms.L2Operator

theorem hermitian_trace_im_zero {d} (M : Mat d) (hM : M.IsHermitian) : M.trace.im = 0 := by
  have ht := congrArg Matrix.trace hM.eq
  rw [Matrix.trace_conjTranspose] at ht
  have hi := congrArg Complex.im ht
  simp only [Complex.star_def, Complex.conj_im] at hi
  linarith

theorem weightedSquare_eq_zero {d} (A M : Mat d) (hA : A.PosDef)
    (hz : reTrace (M.conjTranspose * A * M) = 0) : M = 0 := by
  let S := CFC.sqrt A
  have hSP : S.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)
  have hS : S.conjTranspose = S := hSP.isHermitian.eq
  have hSS : S*S = A := CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg
  have hSM : reTrace ((S*M).conjTranspose * (S*M)) = 0 := by
    have hex : (S*M).conjTranspose * (S*M) = M.conjTranspose * A * M := by
      rw [Matrix.conjTranspose_mul, hS]
      calc
        M.conjTranspose * S * (S*M) = M.conjTranspose * (S*S) * M := by
          noncomm_ring
        _ = _ := by rw [hSS]
    rw [hex]
    exact hz
  have hi := hermitian_trace_im_zero _ (Matrix.isHermitian_conjTranspose_mul_self (S*M))
  have ht : ((S*M).conjTranspose * (S*M)).trace = 0 := by
    apply Complex.ext
    · exact hSM
    · exact hi
  have hzero : S*M = 0 := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp ht
  have hAM : A*M = 0 := by rw [← hSS, mul_assoc, hzero, mul_zero]
  exact hA.isUnit.mul_left_cancel (by simpa only [mul_zero] using hAM)

/-- Fuglede and the positive square root replace the normal spectral argument. -/
theorem normal_product_commutes {d} (A B : Mat d) (hA : A.PosSemidef)
    (hB : B.IsHermitian) (hn : IsStarNormal (A*B)) : Commute A B := by
  have hstar : star (A*B) = B*A := by
    simp only [star_mul, Matrix.star_eq_conjTranspose, hA.isHermitian.eq, hB.eq]
  have hn' : IsStarNormal (B*A) := by rw [← hstar]; exact hn.star
  have hs : SemiconjBy A (B*A) (A*B) := by simp [SemiconjBy, mul_assoc]
  have hf := hs.star_right hn' hn
  have hf' : A*A*B = B*A*A := by
    simpa only [SemiconjBy, star_mul, Matrix.star_eq_conjTranspose,
      hA.isHermitian.eq, hB.eq, mul_assoc] using hf
  have hc : Commute (A*A) B := by simpa only [Commute, SemiconjBy, mul_assoc] using hf'
  have hsqrt := hc.cfcₙ_nnreal NNReal.sqrt
  change Commute (CFC.sqrt (A*A)) B at hsqrt
  rw [CFC.sqrt_mul_self A hA.nonneg] at hsqrt
  exact hsqrt

theorem w54_zero_of_equality {d} (A B : Mat d) (hA : A.PosDef) (hB : B.IsHermitian)
    (heq : p 5 4 A B = reTrace (A*(A*B)^4)) :
    evalPoly A B w1 = 0 ∧ evalPoly A B w2 = 0 ∧
      evalPoly A B w3 = 0 ∧ evalPoly A B w4 = 0 := by
  have hid := identity54 A B hA.isHermitian hB
  have hword : trWord A B [false,false,true,false,true,false,true,false,true] =
      reTrace (A*(A*B)^4) := by simp [trWord, evalWord, pow_succ, mul_assoc]
  rw [hword, heq, sub_self, mul_zero] at hid
  have h1 := matrix_weightedSquare_nonneg A (evalPoly A B w1) hA.posSemidef
  have h2 := matrix_weightedSquare_nonneg A (evalPoly A B w2) hA.posSemidef
  have h3 := matrix_weightedSquare_nonneg A (evalPoly A B w3) hA.posSemidef
  have h4 := matrix_weightedSquare_nonneg A (evalPoly A B w4) hA.posSemidef
  exact ⟨weightedSquare_eq_zero A _ hA (by linarith),
    weightedSquare_eq_zero A _ hA (by linarith),
    weightedSquare_eq_zero A _ hA (by linarith),
    weightedSquare_eq_zero A _ hA (by linarith)⟩

theorem equality54_imp_commute {d} (A B : Mat d) (hA : A.PosDef) (hB : B.IsHermitian)
    (heq : p 5 4 A B = reTrace (A*(A*B)^4)) : Commute A B := by
  obtain ⟨_, hw2, hw3, hw4⟩ := w54_zero_of_equality A B hA hB heq
  have hv4 : evalPoly A B v4 = 0 := hw4
  have hv3 : evalPoly A B v3 = 0 := by
    simpa only [w3, evalPoly_add, evalPoly_scale, hv4, smul_zero, add_zero] using hw3
  have hv2 : evalPoly A B v2 = 0 := by
    simpa only [w2, evalPoly_add, evalPoly_scale, hv3, hv4,
      smul_zero, zero_add, add_zero] using hw2
  have hn : IsStarNormal (A*B) := by
    refine ⟨?_⟩
    change star (A*B) * (A*B) = (A*B) * star (A*B)
    simp only [star_mul, Matrix.star_eq_conjTranspose, hA.isHermitian.eq, hB.eq]
    have hv : B*A*A*B - A*B*B*A = 0 := by
      simpa [v2, u4, u3, evalWord, mul_assoc, sub_eq_add_neg] using hv2
    simpa only [mul_assoc] using sub_eq_zero.mp hv
  exact normal_product_commutes A B hA.posSemidef hB hn

theorem commute54_equality {d} (A B : Mat d) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hc : Commute A B) : p 5 4 A B = reTrace (A*(A*B)^4) := by
  have hid := identity54 A B hA hB
  have hword : trWord A B [false,false,true,false,true,false,true,false,true] =
      reTrace (A*(A*B)^4) := by simp [trWord, evalWord, pow_succ, mul_assoc]
  have hu : evalPoly A B u1 = A^2*B^2 ∧ evalPoly A B u2 = A^2*B^2 ∧
      evalPoly A B u3 = A^2*B^2 ∧ evalPoly A B u4 = A^2*B^2 ∧
      evalPoly A B u5 = A^2*B^2 ∧ evalPoly A B u6 = A^2*B^2 := by
    have hab : B*A = A*B := hc.eq.symm
    have hbAA : B*(A*A) = (A*A)*B := by simpa only [pow_two] using (hc.pow_left 2).eq.symm
    simp [u1, u2, u3, u4, u5, u6, evalWord, pow_two, ← mul_assoc, hab, hbAA]
  obtain ⟨hu1, hu2, hu3, hu4, hu5, hu6⟩ := hu
  have hv1 : evalPoly A B v1 = 0 := by simp [v1, hu1, hu2, hu3]; module
  have hv2 : evalPoly A B v2 = 0 := by simp [v2, hu4, hu3]
  have hv3 : evalPoly A B v3 = 0 := by simp [v3, hu5, hu3]
  have hv4 : evalPoly A B v4 = 0 := by simp [v4, hu6, hu3]
  simp [w1, w2, w3, w4, hv1, hv2, hv3, hv4] at hid
  rw [hword] at hid
  linarith

theorem equality54_iff_commute {d} (A B : Mat d) (hA : A.PosDef) (hB : B.IsHermitian) :
    p 5 4 A B = reTrace (A*(A*B)^4) ↔ Commute A B :=
  ⟨equality54_imp_commute A B hA hB, commute54_equality A B hA.isHermitian hB⟩

end RefinedBMV
