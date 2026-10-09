import RefinedBMV.CubicCenter

namespace RefinedBMV
open scoped ComplexOrder MatrixOrder
set_option maxHeartbeats 500000

def hsSquared {d} (M : Mat d) : ℝ := reTrace (star M*M)
def hsFourth {d} (M : Mat d) : ℝ := reTrace ((star M*M)^2)

theorem hsSquared_nonneg {d} (M : Mat d) : 0 ≤ hsSquared M := by
  exact (RCLike.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self M).trace_nonneg).1

theorem hsFourth_nonneg {d} (M : Mat d) : 0 ≤ hsFourth M := by
  exact (RCLike.nonneg_iff.mp ((Matrix.posSemidef_conjTranspose_mul_self M).pow 2).trace_nonneg).1

theorem hsSquared_star {d} (M : Mat d) : hsSquared (star M) = hsSquared M := by
  simp only [hsSquared, star_star]
  exact reTrace_cycle _ _

theorem hsFourth_star {d} (M : Mat d) : hsFourth (star M) = hsFourth M := by
  simp only [hsFourth, star_star]
  exact reTrace_mul_pow _ _ 2

/-- Hilbert--Schmidt Cauchy--Schwarz for the complete complex trace. -/
theorem trace_cauchy_schwarz {d} (M N : Mat d) :
    ‖(M*N).trace‖^2 ≤ hsSquared M*hsSquared N := by
  let : SeminormedAddCommGroup (Mat d) :=
    (1 : Mat d).toMatrixSeminormedAddCommGroup Matrix.PosSemidef.one
  let : InnerProductSpace ℂ (Mat d) :=
    (1 : Mat d).toMatrixInnerProductSpace Matrix.PosSemidef.one
  have h := norm_inner_le_norm (𝕜 := ℂ) (star M) N
  have hi : inner ℂ (star M) N = (M*N).trace := by
    change (N*1*(star M).conjTranspose).trace = _
    simp only [mul_one, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
    exact Matrix.trace_mul_comm _ _
  have hM : ‖star M‖^2 = hsSquared M := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
    change reTrace (star M*1*(star M).conjTranspose) = _
    simp only [mul_one, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
    rfl
  have hN : ‖N‖^2 = hsSquared N := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
    change reTrace (N*1*N.conjTranspose) = _
    rw [mul_one, reTrace_cycle]
    rfl
  rw [hi] at h
  calc
    ‖(M*N).trace‖^2 ≤ (‖star M‖*‖N‖)^2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = hsSquared M*hsSquared N := by rw [mul_pow,hM,hN]

theorem hermitian_trace_cauchy {d} (M N : Mat d) (hM : M.IsHermitian) (hN : N.IsHermitian) :
    (reTrace (M*N))^2 ≤ reTrace (M^2)*reTrace (N^2) := by
  have h := trace_cauchy_schwarz M N
  have he : (reTrace (M*N))^2 ≤ ‖(M*N).trace‖^2 := by
    have hn := Complex.sq_norm_sub_sq_re (M*N).trace
    dsimp [reTrace]
    nlinarith only [hn, sq_nonneg (M*N).trace.im]
  have hMS : hsSquared M = reTrace (M^2) := by
    simp only [hsSquared, Matrix.star_eq_conjTranspose, hM.eq, pow_two]
  have hNS : hsSquared N = reTrace (N^2) := by
    simp only [hsSquared, Matrix.star_eq_conjTranspose, hN.eq, pow_two]
  rw [hMS,hNS] at h
  exact he.trans h

/-- The 4/4 product estimate, squared to avoid any fractional norm convention. -/
theorem hsSquared_product_le {d} (M N : Mat d) :
    (hsSquared (M*N))^2 ≤ hsFourth M*hsFourth N := by
  have h := hermitian_trace_cauchy (star M*M) (N*star N)
    (Matrix.isHermitian_conjTranspose_mul_self M) (Matrix.isHermitian_mul_conjTranspose_self N)
  have he : hsSquared (M*N) = reTrace ((star M*M)*(N*star N)) := by
    simp only [hsSquared, star_mul]
    rw [mul_assoc, reTrace_cycle (star N)]
    simp only [mul_assoc]
  rw [he]
  rw [reTrace_mul_pow N (star N) 2] at h
  exact h

/-- Schatten Holder at 4,4,2, expressed entirely in positive trace moments. -/
theorem trace_holder_442 {d} (M N Q : Mat d) :
    ‖(M*N*Q).trace‖^4 ≤ hsFourth M*hsFourth N*(hsSquared Q)^2 := by
  have h1 := trace_cauchy_schwarz (M*N) Q
  have h2 := hsSquared_product_le M N
  calc
    ‖(M*N*Q).trace‖^4 = (‖(M*N*Q).trace‖^2)^2 := by ring
    _ ≤ (hsSquared (M*N)*hsSquared Q)^2 := pow_le_pow_left₀ (sq_nonneg _) h1 2
    _ = (hsSquared (M*N))^2*(hsSquared Q)^2 := by ring
    _ ≤ hsFourth M*hsFourth N*(hsSquared Q)^2 :=
      mul_le_mul_of_nonneg_right h2 (sq_nonneg _)

end RefinedBMV
