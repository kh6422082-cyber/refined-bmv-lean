import RefinedBMV.LowDegree
import Mathlib.Analysis.Matrix.Order

namespace RefinedBMV
open scoped ComplexOrder MatrixOrder

theorem twoWeightedSquare_nonneg {d} (L R M : Mat d)
    (hL : L.PosSemidef) (hR : R.PosSemidef) :
    0 ≤ reTrace (M.conjTranspose * L * M * R) := by
  let S : Mat d := CFC.sqrt R
  have hSP : (CFC.sqrt R).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg R)
  have hS : S.conjTranspose = S := hSP.isHermitian.eq
  have hSS : S * S = R := CFC.sqrt_mul_sqrt_self R hR.nonneg
  have hh := matrix_weightedSquare_nonneg L (M * S) hL
  rw [Matrix.conjTranspose_mul, hS] at hh
  calc
    0 ≤ reTrace (S * (M.conjTranspose * L * M * S)) := by
      simpa only [mul_assoc] using hh
    _ = reTrace ((M.conjTranspose * L * M * S) * S) := reTrace_cycle _ _
    _ = reTrace (M.conjTranspose * L * M * R) := by
      simp only [mul_assoc, hSS]

theorem poly_square_nonneg {d} (A B : Mat d) (hA : A.IsHermitian)
    (hB : B.IsHermitian) (v : Poly) (l r : Word)
    (hl : (evalWord A B l).PosSemidef) (hr : (evalWord A B r).PosSemidef) :
    0 ≤ reTrace (evalPoly A B (weightedSquare v l r)) := by
  rw [evalPoly_weightedSquare A B hA hB]
  exact twoWeightedSquare_nonneg _ _ _ hl hr

theorem p54_ge_U {d} (A B : Mat d) (hA : A.PosSemidef) (hB : B.IsHermitian) :
    reTrace (A * (A * B)^4) ≤ p 5 4 A B := by
  simpa [trWord, evalWord, pow_succ, mul_assoc] using p54_ge_alternating A B hA hB

theorem p43_ge_W {d} (A B : Mat d) (hA : A.IsHermitian) (hB : B.PosSemidef) :
    reTrace (A^2 * B * A * B * A * B) ≤ p 4 3 A B := by
  simpa [trWord, evalWord, pow_succ, mul_assoc] using p43_ge_word A B hA hB

end RefinedBMV
