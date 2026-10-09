import RefinedBMV.MatrixSquares
import RefinedBMV.GramPositivity

namespace RefinedBMV
open scoped ComplexOrder
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def s44_0 : Poly := add (scale (1) (g0_0)) (add (scale (-43/34) (g0_1)) (add (scale (67/34) (g0_2)) (add (scale (-4/3) (g0_3)) (scale (-67/51) (g0_4)))))
def s44_1 : Poly := add (scale (1) (g0_1)) (add (scale (-3427/4415) (g0_2)) (add (scale (-391/4415) (g0_3)) (scale (-78/883) (g0_4))))
def s44_2 : Poly := add (scale (1) (g0_2)) (add (scale (-368328/704959) (g0_3)) (scale (-727105/1409918) (g0_4)))
def s44_3 : Poly := add (scale (1) (g0_3)) (scale (5472554/8710789) (g0_4))
def s44_4 : Poly := scale (1) (g0_4)
def sos44 : Poly := add (scale (102/5) (weightedSquare s44_0 [] [])) (add (scale (883/34) (weightedSquare s44_1 [] [])) (add (scale (704959/22075) (weightedSquare s44_2 [] [])) (add (scale (8710789/21148770) (weightedSquare s44_3 [] [])) (add (scale (58147803/174215780) (weightedSquare s44_4 [] [])) (add (scale (1/5) (weightedSquare g1_0 [false] [false])) (add (scale (129/5) (weightedSquare g1_1 [false] [false])) (add (scale (1/5) (weightedSquare g2_0 [true] [true])) (scale (297/5) (weightedSquare g2_1 [true] [true])))))))))
def residual44sos : Poly := add (scale 560 (add (average 4 4) (scale (-1) jordan4))) (scale (-1) sos44)
theorem certificate44sos : zeroCertificate residual44sos := by decide +kernel

theorem sos44_nonneg {d} (A B : Mat d) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ reTrace (evalPoly A B sos44) := by
  have h0 := poly_square_nonneg A B hA.isHermitian hB.isHermitian s44_0 [] [] (by simpa [evalWord] using (Matrix.PosSemidef.one : (1 : Mat d).PosSemidef)) (by simpa [evalWord] using (Matrix.PosSemidef.one : (1 : Mat d).PosSemidef))
  have h1 := poly_square_nonneg A B hA.isHermitian hB.isHermitian s44_1 [] [] (by simpa [evalWord] using (Matrix.PosSemidef.one : (1 : Mat d).PosSemidef)) (by simpa [evalWord] using (Matrix.PosSemidef.one : (1 : Mat d).PosSemidef))
  have h2 := poly_square_nonneg A B hA.isHermitian hB.isHermitian s44_2 [] [] (by simpa [evalWord] using (Matrix.PosSemidef.one : (1 : Mat d).PosSemidef)) (by simpa [evalWord] using (Matrix.PosSemidef.one : (1 : Mat d).PosSemidef))
  have h3 := poly_square_nonneg A B hA.isHermitian hB.isHermitian s44_3 [] [] (by simpa [evalWord] using (Matrix.PosSemidef.one : (1 : Mat d).PosSemidef)) (by simpa [evalWord] using (Matrix.PosSemidef.one : (1 : Mat d).PosSemidef))
  have h4 := poly_square_nonneg A B hA.isHermitian hB.isHermitian s44_4 [] [] (by simpa [evalWord] using (Matrix.PosSemidef.one : (1 : Mat d).PosSemidef)) (by simpa [evalWord] using (Matrix.PosSemidef.one : (1 : Mat d).PosSemidef))
  have h5 := poly_square_nonneg A B hA.isHermitian hB.isHermitian g1_0 [false] [false] (by simpa [evalWord] using hA) (by simpa [evalWord] using hA)
  have h6 := poly_square_nonneg A B hA.isHermitian hB.isHermitian g1_1 [false] [false] (by simpa [evalWord] using hA) (by simpa [evalWord] using hA)
  have h7 := poly_square_nonneg A B hA.isHermitian hB.isHermitian g2_0 [true] [true] (by simpa [evalWord] using hB) (by simpa [evalWord] using hB)
  have h8 := poly_square_nonneg A B hA.isHermitian hB.isHermitian g2_1 [true] [true] (by simpa [evalWord] using hB) (by simpa [evalWord] using hB)
  simp only [sos44, evalPoly_add, evalPoly_scale, reTrace_add, reTrace_smul]
  norm_num
  linarith

theorem evalPoly_jordan4 {d} (A B : Mat d) :
    evalPoly A B jordan4 = ((1/2 : ℝ) • (A * B + B * A))^4 := by
  norm_num [jordan4, jordan, evalWord, pow_succ, mul_assoc]

/-- The all-dimensional Jordan intermediate lower bound, including singular inputs. -/
theorem p44_ge_jordan {d} (A B : Mat d) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    reTrace (((1/2 : ℝ) • (A * B + B * A))^4) ≤ p 4 4 A B := by
  have h := tracePoly_zero_of_certificate A B hA.isHermitian hB.isHermitian
    residual44sos certificate44sos
  simp only [residual44sos, evalPoly_add, evalPoly_scale, reTrace_add, reTrace_smul] at h
  norm_num at h
  have hs := sos44_nonneg A B hA hB
  rw [evalPoly_jordan4] at h
  unfold p
  linarith

end RefinedBMV
