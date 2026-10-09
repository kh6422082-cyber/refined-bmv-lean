import RefinedBMV.CubicMatrix

namespace RefinedBMV
open scoped ComplexOrder MatrixOrder
set_option maxHeartbeats 500000

open scoped Matrix.Norms.L2Operator in
/-- Finite-dimensional polar decomposition for invertible complex matrices. -/
theorem invertible_polar {d} (M : Mat d) (hM : IsUnit M) :
    ∃ U P : Mat d, U ∈ unitary (Mat d) ∧ P.PosDef ∧ M = U*P ∧ P*P = star M*M := by
  let P := CFC.sqrt (star M*M)
  have hH : (star M*M).PosDef :=
    (Matrix.posSemidef_conjTranspose_mul_self M).posDef_iff_isUnit.mpr (hM.star.mul hM)
  have hP : P.PosDef := Matrix.isStrictlyPositive_iff_posDef.mp
    (IsStrictlyPositive.sqrt (star M*M) hH.isStrictlyPositive)
  have hPP : P*P = star M*M := CFC.sqrt_mul_sqrt_self _ hH.posSemidef.nonneg
  obtain ⟨v,hv⟩ := hP.isUnit
  have hvstar : star v = v := by
    apply Units.ext
    change star (v : Mat d) = (v : Mat d)
    rw [hv]
    exact hP.isHermitian.eq
  have hivstar : star ((v⁻¹ : (Mat d)ˣ) : Mat d) = ((v⁻¹ : (Mat d)ˣ) : Mat d) := by
    change ((star (v⁻¹) : (Mat d)ˣ) : Mat d) = _
    rw [star_inv,hvstar]
  let U := M*((v⁻¹ : (Mat d)ˣ) : Mat d)
  have hU : IsUnit U := hM.mul (Units.isUnit v⁻¹)
  have hUU : star U*U = 1 := by
    calc
      star U*U = (star ((v⁻¹ : (Mat d)ˣ) : Mat d)*(star M*M))*
          ((v⁻¹ : (Mat d)ˣ) : Mat d) := by simp only [U,star_mul,mul_assoc]
      _ = (((v⁻¹ : (Mat d)ˣ) : Mat d)*P)*(P*((v⁻¹ : (Mat d)ˣ) : Mat d)) := by
        rw [hivstar,← hPP]
        simp only [mul_assoc]
      _ = 1 := by rw [← hv]; simp
  have hmem : U ∈ unitary (Mat d) := hU.mem_unitary_iff_star_mul_self.mpr hUU
  refine ⟨U,P,hmem,hP,?_,hPP⟩
  dsimp [U]
  rw [← hv]
  simp

theorem hsFourth_left_unitary {d} (U M : Mat d) (hU : U ∈ unitary (Mat d)) :
    hsFourth (U*M) = hsFourth M := by
  rw [← hsFourth_star (U*M),star_mul,hsFourth_right_unitary _ _ (Unitary.star_mem hU),hsFourth_star]

/-- A positive weight against an arbitrary unitary has trace modulus at most its trace. -/
theorem positive_unitary_trace_bound {d} (H U : Mat d) (hH : H.PosSemidef)
    (hU : U ∈ unitary (Mat d)) : ‖(H*U).trace‖ ≤ reTrace H := by
  let : SeminormedAddCommGroup (Mat d) := H.toMatrixSeminormedAddCommGroup hH
  let : InnerProductSpace ℂ (Mat d) := H.toMatrixInnerProductSpace hH
  have hi : inner ℂ (star U) (1 : Mat d) = (H*U).trace := by
    change (1*H*(star U).conjTranspose).trace = _
    simp only [one_mul,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_conjTranspose]
  have h1 : ‖(1 : Mat d)‖^2 = reTrace H := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
    change reTrace (1*H*(1 : Mat d).conjTranspose) = _
    simp only [Matrix.conjTranspose_one,one_mul,mul_one]
  have hnormU : ‖star U‖^2 = reTrace H := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
    change reTrace (star U*H*(star U).conjTranspose) = _
    simp only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_conjTranspose]
    have he := reTrace_unitary_reverse_conj_pow U H hU 1
    simpa only [pow_one,Matrix.star_eq_conjTranspose] using he
  have h := norm_inner_le_norm (𝕜 := ℂ) (star U) (1 : Mat d)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [hi,mul_pow,hnormU,h1] at hsq
  have hnonneg : 0 ≤ reTrace H := (RCLike.nonneg_iff.mp hH.trace_nonneg).1
  apply (sq_le_sq₀ (norm_nonneg _) hnonneg).mp
  simpa only [pow_two] using hsq

end RefinedBMV
