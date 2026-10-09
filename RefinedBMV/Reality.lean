import RefinedBMV.WordStructure

namespace RefinedBMV
open scoped ComplexOrder MatrixOrder

theorem weighted_sandwich_trace_complex {d} (A B : Mat d) (hA : A.PosSemidef) :
    Matrix.trace ((CFC.sqrt A * B * CFC.sqrt A)^4 * A) = Matrix.trace (A * (A * B)^4) := by
  let S := CFC.sqrt A
  have hSS : S*S = A := CFC.sqrt_mul_sqrt_self A hA.nonneg
  have he : (S*B*S)^4 = S * (B*(S*S))^3 * B * S := by noncomm_ring
  change Matrix.trace ((S*B*S)^4 * A) = _
  rw [he]
  calc
    Matrix.trace (S * (B*(S*S))^3 * B * S * A) =
        Matrix.trace (S * ((B*(S*S))^3 * B * (S * A))) := by simp [mul_assoc]
    _ = Matrix.trace (((B*(S*S))^3 * B * (S * A)) * S) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace ((B*A)^3 * B * (S*A*S)) := by simp [mul_assoc, hSS]
    _ = Matrix.trace ((B*A)^4 * A) := by
      have hsas : S*A*S = A*A := by rw [← hSS]; noncomm_ring
      rw [hsas]
      simp [pow_succ, mul_assoc]
    _ = Matrix.trace (A * (A*B)^4) := by
      have hc : (B*A)^4 * A = ((B*A)^3 * B) * (A*A) := by simp [pow_succ, mul_assoc]
      rw [hc, Matrix.trace_mul_comm]
      simp [pow_succ, mul_assoc]

theorem hermitian_product_trace_real {d} (M N : Mat d)
    (hM : M.IsHermitian) (hN : N.IsHermitian) : (M*N).trace.im = 0 := by
  have he : star (M*N).trace = (M*N).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hM.eq, hN.eq,
      Matrix.trace_mul_comm]
  have hi := congrArg Complex.im he
  simp only [Complex.star_def, Complex.conj_im] at hi
  linarith

theorem alternating54_trace_real {d} (A B : Mat d)
    (hA : A.PosSemidef) (hB : B.IsHermitian) : (A*(A*B)^4).trace.im = 0 := by
  have hs : (CFC.sqrt A).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian
  have hj := sandwich_isHermitian _ _ hs hB
  have he := hermitian_product_trace_real _ A (hj.pow 4) hA.isHermitian
  rw [weighted_sandwich_trace_complex A B hA] at he
  exact he

theorem trace_mul_pow_complex {d} (X Y : Mat d) (k : ℕ) :
    ((X*Y)^k).trace = ((Y*X)^k).trace := by
  cases k with
  | zero => simp
  | succ k =>
    rw [mul_pow_factor]
    calc
      (X * (Y*X)^k * Y).trace = (X * ((Y*X)^k * Y)).trace := by rw [mul_assoc]
      _ = (((Y*X)^k * Y) * X).trace := Matrix.trace_mul_comm _ _
      _ = ((Y*X)^(k+1)).trace := by simp [pow_succ, mul_assoc]

theorem product44_trace_real {d} (A B : Mat d)
    (hA : A.PosSemidef) (hB : B.IsHermitian) : ((A*B)^4).trace.im = 0 := by
  have hs : (CFC.sqrt A).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian
  have hj := sandwich_isHermitian _ _ hs hB
  have he := trace_mul_pow_complex (CFC.sqrt A) (CFC.sqrt A * B) 4
  have ht : ((A*B)^4).trace = ((CFC.sqrt A * B * CFC.sqrt A)^4).trace := by
    simpa only [← mul_assoc, CFC.sqrt_mul_sqrt_self A hA.nonneg] using he
  rw [ht]
  exact hermitian_trace_im_zero _ (hj.pow 4)

end RefinedBMV
