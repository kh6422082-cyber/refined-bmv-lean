import RefinedBMV.PolarTrace

namespace RefinedBMV
open scoped ComplexOrder MatrixOrder
set_option maxHeartbeats 500000

def hsEighth {d} (M : Mat d) : ℝ := reTrace ((star M*M)^4)

theorem hsEighth_nonneg {d} (M : Mat d) : 0 ≤ hsEighth M :=
  (RCLike.nonneg_iff.mp ((Matrix.posSemidef_conjTranspose_mul_self M).pow 4).trace_nonneg).1

theorem hsEighth_star {d} (M : Mat d) : hsEighth (star M) = hsEighth M := by
  simp only [hsEighth,star_star]
  exact reTrace_mul_pow _ _ 4

/-- The next dyadic Schatten product estimate, obtained from two Hilbert--Schmidt steps. -/
theorem hsFourth_product_le {d} (M N : Mat d) :
    (hsFourth (M*N))^2 ≤ hsEighth M*hsEighth N := by
  let H := star M*M
  let K := N*star N
  have hH : H.IsHermitian := Matrix.isHermitian_conjTranspose_mul_self M
  have hK : K.IsHermitian := Matrix.isHermitian_mul_conjTranspose_self N
  have he : hsFourth (M*N) = reTrace ((H*K)^2) := by
    have h := reTrace_mul_pow (star N) (star M*M*N) 2
    simpa only [hsFourth,star_mul,H,K,mul_assoc] using h
  have hc := commutator_second_moment_identity H K hH hK
  have hzero : 0 ≤ reTrace ((H*K-K*H).conjTranspose*(H*K-K*H)) := hsSquared_nonneg _
  have hbound : hsFourth (M*N) ≤ reTrace (H^2*K^2) := by rw [he]; linarith
  have hcs := hermitian_trace_cauchy (H^2) (K^2) (hH.pow 2) (hK.pow 2)
  have hpowH : (H^2)^2 = H^4 := by noncomm_ring
  have hpowK : (K^2)^2 = K^4 := by noncomm_ring
  rw [hpowH,hpowK] at hcs
  have hK4 : reTrace (K^4) = hsEighth N := reTrace_mul_pow N (star N) 4
  rw [hK4] at hcs
  exact (pow_le_pow_left₀ (hsFourth_nonneg _) hbound 2).trans hcs

theorem hsEighth_right_unitary {d} (M U : Mat d) (hU : U ∈ unitary (Mat d)) :
    hsEighth (M*U) = hsEighth M := by
  have he : star (M*U)*(M*U) = star U*(star M*M)*U := by
    rw [star_mul]
    simp only [mul_assoc]
  rw [hsEighth,he]
  exact reTrace_unitary_reverse_conj_pow U (star M*M) hU 4

theorem hsEighth_left_unitary {d} (U M : Mat d) (hU : U ∈ unitary (Mat d)) :
    hsEighth (U*M) = hsEighth M := by
  rw [← hsEighth_star (U*M),star_mul,hsEighth_right_unitary _ _ (Unitary.star_mem hU),hsEighth_star]

/-- Schatten Holder at 8,8,4,2 in positive trace-moment form. -/
theorem trace_holder_8842 {d} (M N R Q : Mat d) :
    ‖(M*N*R*Q).trace‖^8 ≤ hsEighth M*hsEighth N*(hsFourth R)^2*(hsSquared Q)^4 := by
  have h1 := trace_cauchy_schwarz (M*N*R) Q
  have h2 := hsSquared_product_le (M*N) R
  have h3 := hsFourth_product_le M N
  have hh : (hsSquared (M*N*R))^4 ≤ hsEighth M*hsEighth N*(hsFourth R)^2 := by
    calc
      (hsSquared (M*N*R))^4 = ((hsSquared (M*N*R))^2)^2 := by ring
      _ ≤ (hsFourth (M*N)*hsFourth R)^2 := pow_le_pow_left₀ (sq_nonneg _) h2 2
      _ = (hsFourth (M*N))^2*(hsFourth R)^2 := by ring
      _ ≤ hsEighth M*hsEighth N*(hsFourth R)^2 := mul_le_mul_of_nonneg_right h3 (sq_nonneg _)
  calc
    ‖(M*N*R*Q).trace‖^8 = (‖(M*N*R*Q).trace‖^2)^4 := by ring
    _ ≤ (hsSquared (M*N*R)*hsSquared Q)^4 := pow_le_pow_left₀ (sq_nonneg _) h1 4
    _ = (hsSquared (M*N*R))^4*(hsSquared Q)^4 := by ring
    _ ≤ hsEighth M*hsEighth N*(hsFourth R)^2*(hsSquared Q)^4 :=
      mul_le_mul_of_nonneg_right hh (pow_nonneg (hsSquared_nonneg _) _)

end RefinedBMV
