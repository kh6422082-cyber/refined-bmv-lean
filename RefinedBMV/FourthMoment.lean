import RefinedBMV.MatrixSquares

namespace RefinedBMV
open scoped ComplexOrder
open scoped MatrixOrder
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def z4_1 : Poly := add (atom [false,true,false,true]) (scale (-1) (atom [true,false,true,false]))
def z4_2 : Poly := add (atom [false,true,true,false]) (scale (-1) (atom [true,false,false,true]))
def z4_3 : Poly := add (atom [false,false,true,true]) (scale (-1) (atom [true,true,false,false]))
def fourthSOS : Poly := scale (1/2) (add (weightedSquare z4_1 [] [])
  (add (weightedSquare z4_2 [] []) (weightedSquare z4_3 [] [])))
def fourthResidual : Poly := add
  (add (atom [false,false,false,false,true,true,true,true])
    (scale (-1) (atom [false,true,false,true,false,true,false,true])))
  (scale (-1) fourthSOS)
theorem fourthCertificate : zeroCertificate fourthResidual := by decide +kernel

/-- Three ordinary Hilbert--Schmidt squares give the fourth-moment comparison. -/
theorem fourth_moment_le {d} (J C : Mat d) (hJ : J.IsHermitian) (hC : C.IsHermitian) :
    reTrace ((J*C)^4) ≤ reTrace (J^4 * C^4) := by
  have h := tracePoly_zero_of_certificate J C hJ hC fourthResidual fourthCertificate
  simp only [fourthResidual, fourthSOS, evalPoly_add, evalPoly_scale,
    evalPoly_atom, reTrace_add, reTrace_smul] at h
  norm_num at h
  have h1 := poly_square_nonneg J C hJ hC z4_1 [] []
    (by simp [evalWord]; exact Matrix.PosSemidef.one)
    (by simp [evalWord]; exact Matrix.PosSemidef.one)
  have h2 := poly_square_nonneg J C hJ hC z4_2 [] []
    (by simp [evalWord]; exact Matrix.PosSemidef.one)
    (by simp [evalWord]; exact Matrix.PosSemidef.one)
  have h3 := poly_square_nonneg J C hJ hC z4_3 [] []
    (by simp [evalWord]; exact Matrix.PosSemidef.one)
    (by simp [evalWord]; exact Matrix.PosSemidef.one)
  simp only [evalWord, ite_true, mul_one] at h
  have he1 : (J*C)^4 = evalWord J C [false,true,false,true,false,true,false,true] := by
    simp [evalWord, pow_succ, mul_assoc]
  have he2 : J^4 * C^4 = evalWord J C [false,false,false,false,true,true,true,true] := by
    simp [evalWord, pow_succ, mul_assoc]
  simp only [he1, he2, evalWord, ite_true, mul_one]
  linarith

theorem mul_pow_factor {d} (X Y : Mat d) (k : ℕ) :
    (X*Y)^(k+1) = X * (Y*X)^k * Y := by
  induction k with
  | zero => simp
  | succ k ih => simp only [pow_succ, ih, mul_assoc]

theorem reTrace_mul_pow {d} (X Y : Mat d) (k : ℕ) :
    reTrace ((X*Y)^k) = reTrace ((Y*X)^k) := by
  cases k with
  | zero => simp
  | succ k =>
    rw [mul_pow_factor]
    calc
      reTrace (X * (Y*X)^k * Y) = reTrace (X * ((Y*X)^k * Y)) := by
        rw [mul_assoc]
      _ = reTrace (((Y*X)^k * Y) * X) := reTrace_cycle _ _
      _ = reTrace ((Y*X)^(k+1)) := by simp [pow_succ, mul_assoc]

/-- This is exactly the analytic comparison lemma (54.5) in the latest manuscript. -/
theorem sandwich_fourth_le {d} (J C : Mat d)
    (hJ : J.IsHermitian) (hC : C.PosSemidef) :
    reTrace ((CFC.sqrt C * J * CFC.sqrt C)^4) ≤ reTrace (J^4 * C^4) := by
  have hs : CFC.sqrt C * CFC.sqrt C = C := CFC.sqrt_mul_sqrt_self C hC.nonneg
  have he := reTrace_mul_pow (CFC.sqrt C) (J * CFC.sqrt C) 4
  simp only [mul_assoc, hs] at he
  rw [show reTrace ((CFC.sqrt C * J * CFC.sqrt C)^4) = reTrace ((J*C)^4) by
    simpa only [mul_assoc] using he]
  exact fourth_moment_le J C hJ hC.isHermitian

end RefinedBMV
