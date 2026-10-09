import RefinedBMV.Certificates

namespace RefinedBMV
open scoped ComplexOrder

/-- Real trace of the complete average over position-distinct words. -/
noncomputable def p {d : ℕ} (n m : ℕ) (A B : Mat d) : ℝ :=
  reTrace (evalPoly A B (average n m))

theorem rightWeightedSquare_nonneg {d} (M B : Mat d) (hB : B.PosSemidef) :
    0 ≤ reTrace (M.conjTranspose * M * B) := by
  have hh := matrix_weightedSquare_nonneg B M.conjTranspose hB
  calc
    0 ≤ reTrace (M * B * M.conjTranspose) := by
      simpa only [Matrix.conjTranspose_conjTranspose] using hh
    _ = reTrace (M.conjTranspose * M * B) := by
      simpa only [mul_assoc] using reTrace_cycle (M * B) M.conjTranspose

theorem identity43 {d} (A B : Mat d) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    5 * (p 4 3 A B - trWord A B [false,false,true,false,true,false,true]) =
      reTrace ((evalPoly A B (add l43 (scale 2 r43))).conjTranspose *
        evalPoly A B (add l43 (scale 2 r43)) * B) +
      reTrace ((evalPoly A B r43).conjTranspose * evalPoly A B r43 * B) := by
  have h := tracePoly_zero_of_certificate A B hA hB residual43 certificate43
  simp only [residual43, evalPoly_add, evalPoly_scale, evalPoly_atom,
    rhs43, evalPoly_weightedSquare A B hA hB, evalWord,
    Bool.false_eq_true, ite_false, ite_true, mul_one,
    reTrace_add, reTrace_smul] at h
  norm_num at h
  norm_num [p, trWord, evalWord]
  linarith

/-- The first (4,3) comparison; positivity of A is unnecessary for this layer. -/
theorem p43_ge_word {d} (A B : Mat d) (hA : A.IsHermitian) (hB : B.PosSemidef) :
    trWord A B [false,false,true,false,true,false,true] ≤ p 4 3 A B := by
  have h := identity43 A B hA hB.isHermitian
  have h1 := rightWeightedSquare_nonneg (evalPoly A B (add l43 (scale 2 r43))) B hB
  have h2 := rightWeightedSquare_nonneg (evalPoly A B r43) B hB
  linarith

theorem identity54 {d} (A B : Mat d) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    14 * (p 5 4 A B - trWord A B [false,false,true,false,true,false,true,false,true]) =
      reTrace ((evalPoly A B w1).conjTranspose * A * evalPoly A B w1) +
      12 * reTrace ((evalPoly A B w2).conjTranspose * A * evalPoly A B w2) +
      (5/3 : ℝ) * reTrace ((evalPoly A B w3).conjTranspose * A * evalPoly A B w3) +
      (41/10 : ℝ) * reTrace ((evalPoly A B w4).conjTranspose * A * evalPoly A B w4) := by
  have h := tracePoly_zero_of_certificate A B hA hB residual54 certificate54
  simp only [residual54, evalPoly_add, evalPoly_scale, evalPoly_atom,
    rhs54, evalPoly_weightedSquare A B hA hB, evalWord,
    Bool.false_eq_true, ite_false, ite_true, mul_one,
    reTrace_add, reTrace_smul] at h
  norm_num at h
  norm_num [p, trWord, evalWord]
  linarith

theorem identity44 {d} (A B : Mat d) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    560 * (p 4 4 A B - reTrace (evalPoly A B jordan4)) =
      reTrace (evalPoly A B gram0) + reTrace (evalPoly A B gram1) +
        reTrace (evalPoly A B gram2) := by
  have h := tracePoly_zero_of_certificate A B hA hB residual44 certificate44
  simp only [residual44, rhs44, evalPoly_add, evalPoly_scale,
    reTrace_add, reTrace_smul] at h
  norm_num at h
  unfold p
  linarith

/-- Arbitrary finite dimension; A is PSD and B may be indefinite Hermitian. -/
theorem p54_ge_alternating {d} (A B : Mat d) (hA : A.PosSemidef) (hB : B.IsHermitian) :
    trWord A B [false,false,true,false,true,false,true,false,true] ≤ p 5 4 A B := by
  have h := identity54 A B hA.isHermitian hB
  have h1 := matrix_weightedSquare_nonneg A (evalPoly A B w1) hA
  have h2 := matrix_weightedSquare_nonneg A (evalPoly A B w2) hA
  have h3 := matrix_weightedSquare_nonneg A (evalPoly A B w3) hA
  have h4 := matrix_weightedSquare_nonneg A (evalPoly A B w4) hA
  linarith

end RefinedBMV
