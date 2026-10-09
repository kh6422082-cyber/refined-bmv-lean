import RefinedBMV.TraceHolderDyadic
import RefinedBMV.CubicALT

namespace RefinedBMV
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 600000

noncomputable def quarticALTPath {d} (A B P U : Mat d) (z : ℂ) : ℂ :=
  (complexPower A (5*z/8)*complexPower B (5*z/8)*
    complexPower P (10-5*z/4)*star U).trace

theorem quarticALTPath_entire {d} (A B P U : Mat d) : Differentiable ℂ (quarticALTPath A B P U) := by
  let tr : Mat d →L[ℂ] ℂ := (Matrix.traceLinearMap (Fin d) ℂ ℂ).toContinuousLinearMap
  have hz : Differentiable ℂ (fun z : ℂ => 5*z/8) := by fun_prop
  have hpz : Differentiable ℂ (fun z : ℂ => 10-5*z/4) := by fun_prop
  have ha := (complexPower_differentiable A).comp hz
  have hb := (complexPower_differentiable B).comp hz
  have hp := (complexPower_differentiable P).comp hpz
  exact tr.differentiable.comp (((ha.mul hb).mul hp).mul_const (star U))

theorem quarticALTPath_left_bound {d} (A B P U : Mat d) (hP : P.PosDef)
    (hU : U ∈ unitary (Mat d)) (t : ℝ) :
    ‖quarticALTPath A B P U ((t : ℂ)*Complex.I)‖ ≤ reTrace (P^10) := by
  let v : ℂ := (t : ℂ)*Complex.I
  let ua := complexPower A (5*v/8)
  let ub := complexPower B (5*v/8)
  let up := complexPower P (-5*v/4)
  have hua : ua ∈ unitary (Mat d) := complexPower_unitary_of_re_zero A _ (by simp [v])
  have hub : ub ∈ unitary (Mat d) := complexPower_unitary_of_re_zero B _ (by simp [v])
  have hup : up ∈ unitary (Mat d) := complexPower_unitary_of_re_zero P _ (by simp [v])
  have he : complexPower P (10-5*v/4) = P^10*up := by
    rw [← complexPower_nat P hP 10,← complexPower_add]
    congr 1
    ring
  have htrace : quarticALTPath A B P U v = (P^10*(up*star U*ua*ub)).trace := by
    rw [quarticALTPath,he]
    change (ua*ub*(P^10*up)*star U).trace = _
    have hr : ua*ub*(P^10*up)*star U = (ua*ub)*(P^10*up*star U) := by noncomm_ring
    rw [hr,Matrix.trace_mul_comm]
    simp only [mul_assoc]
  rw [htrace]
  exact positive_unitary_trace_bound _ _ (hP.posSemidef.pow 10)
    ((unitary (Mat d)).mul_mem ((unitary (Mat d)).mul_mem
      ((unitary (Mat d)).mul_mem hup (Unitary.star_mem hU)) hua) hub)

theorem hsEighth_five_fourths {d} (P : Mat d) (hP : P.PosDef) :
    hsEighth (complexPower P (5/4)) = reTrace (P^10) := by
  have hs : star (complexPower P (5/4)) = complexPower P (5/4) := by
    rw [complexPower_star]
    norm_num
  rw [hsEighth,hs]
  have he : (complexPower P (5/4)*complexPower P (5/4))^4 = complexPower P 10 := by
    simp only [show (4 : ℕ) = 2+2 from rfl,pow_add,pow_two]
    repeat rw [← complexPower_add]
    norm_num
  rw [he]
  have hn := complexPower_nat P hP 10
  norm_num at hn
  rw [hn]

theorem hsFourth_five_halves {d} (P : Mat d) (hP : P.PosDef) :
    hsFourth (complexPower P (5/2)) = reTrace (P^10) := by
  have hs : star (complexPower P (5/2)) = complexPower P (5/2) := by
    rw [complexPower_star]
    norm_num
  rw [hsFourth,hs,pow_two,← complexPower_add,← complexPower_add]
  norm_num
  have hn := complexPower_nat P hP 10
  norm_num at hn
  rw [hn]

theorem hsSquared_fifth {d} (P : Mat d) (hP : P.IsHermitian) :
    hsSquared (P^5) = reTrace (P^10) := by
  rw [hsSquared,Matrix.star_eq_conjTranspose,(hP.pow 5).eq,← pow_add]

theorem quarticALTPath_right_eighth_bound {d} (A B P U : Mat d) (hP : P.PosDef)
    (hU : U ∈ unitary (Mat d)) (t : ℝ) :
    ‖quarticALTPath A B P U (1+(t : ℂ)*Complex.I)‖^8 ≤
      hsEighth (complexPower A (5/8)*complexPower B (5/8))*(reTrace (P^10))^7 := by
  let v : ℂ := (t : ℂ)*Complex.I
  let ua := complexPower A (5*v/8)
  let ub := complexPower B (5*v/8)
  let up := complexPower P (-5*v/4)
  let M := complexPower A (5/8)*complexPower B (5/8)
  let N := complexPower P (5/4)
  let R := complexPower P (5/2)
  have hua : ua ∈ unitary (Mat d) := complexPower_unitary_of_re_zero A _ (by simp [v])
  have hub : ub ∈ unitary (Mat d) := complexPower_unitary_of_re_zero B _ (by simp [v])
  have hup : up ∈ unitary (Mat d) := complexPower_unitary_of_re_zero P _ (by simp [v])
  have ha : complexPower A (5*(1+v)/8) = ua*complexPower A (5/8) := by
    rw [← complexPower_add]
    congr 1
    ring
  have hb : complexPower B (5*(1+v)/8) = complexPower B (5/8)*ub := by
    rw [← complexPower_add]
    congr 1
    ring
  have hp : complexPower P (10-5*(1+v)/4) = N*R*(P^5*up) := by
    rw [← complexPower_nat P hP 5]
    change complexPower P (10-5*(1+v)/4) =
      complexPower P (5/4)*complexPower P (5/2)*(complexPower P 5*complexPower P (-5*v/4))
    rw [← complexPower_add,← complexPower_add,← complexPower_add]
    congr 1
    ring
  have ht : quarticALTPath A B P U (1+v) = ((ua*M*ub)*N*R*(P^5*up*star U)).trace := by
    rw [quarticALTPath,ha,hb,hp]
    dsimp only [M]
    simp only [mul_assoc]
  have h := trace_holder_8842 (ua*M*ub) N R (P^5*up*star U)
  rw [hsEighth_right_unitary _ _ hub,hsEighth_left_unitary _ _ hua,
    hsSquared_right_unitary _ _ (Unitary.star_mem hU),hsSquared_right_unitary _ _ hup,
    hsEighth_five_fourths P hP,hsFourth_five_halves P hP,hsSquared_fifth P hP.isHermitian] at h
  rw [ht]
  convert h using 1
  ring

theorem quarticALTPath_polar_point {d} (A B P U : Mat d) (hP : P.PosDef)
    (hU : U ∈ unitary (Mat d))
    (hM : complexPower A (1/2)*complexPower B (1/2) = U*P) :
    ‖quarticALTPath A B P U (4/5)‖ = reTrace (P^10) := by
  have ha : (5 : ℂ)*(4/5)/8 = 1/2 := by norm_num
  have hp : (10 : ℂ)-5*(4/5)/4 = 9 := by norm_num
  have h9 := complexPower_nat P hP 9
  norm_num at h9
  rw [quarticALTPath,ha,hp,h9,hM]
  have he : U*P*P^9*star U = U*P^10*star U := by noncomm_ring
  rw [he,Matrix.trace_mul_comm (U*P^10) (star U),← mul_assoc,
    Unitary.star_mul_self_of_mem hU,one_mul]
  have hr : (P^10).trace = (reTrace (P^10) : ℂ) := by
    apply Complex.ext
    · rfl
    · simp only [Complex.ofReal_im]
      exact hermitian_trace_im_zero _ (hP.isHermitian.pow 10)
  have h0 : 0 ≤ reTrace (P^10) := (RCLike.nonneg_iff.mp (hP.posSemidef.pow 10).trace_nonneg).1
  rw [hr,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg h0]

theorem quarticALTPath_bounded_strip {d} (A B P U : Mat d) :
    ∃ K : ℝ, ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → ‖quarticALTPath A B P U z‖ ≤ K := by
  obtain ⟨CA,hCA,bA⟩ := complexPower_bounded_strip A 0 (5/8)
  obtain ⟨CB,hCB,bB⟩ := complexPower_bounded_strip B 0 (5/8)
  obtain ⟨CP,hCP,bP⟩ := complexPower_bounded_strip P (35/4) 10
  let tr : Mat d →L[ℂ] ℂ := (Matrix.traceLinearMap (Fin d) ℂ ℂ).toContinuousLinearMap
  refine ⟨‖tr‖*(CA*CB*CP*‖star U‖),?_⟩
  intro z hlo hhi
  have hrA : (5*z/8).re = 5*z.re/8 := by simp
  have hrP : (10-5*z/4).re = 10-5*z.re/4 := by simp
  have hAr := bA (5*z/8) (by rw [hrA]; linarith) (by rw [hrA]; linarith)
  have hBr := bB (5*z/8) (by rw [hrA]; linarith) (by rw [hrA]; linarith)
  have hPr := bP (10-5*z/4) (by rw [hrP]; linarith) (by rw [hrP]; linarith)
  have ht : ‖complexPower A (5*z/8)*complexPower B (5*z/8)*
      complexPower P (10-5*z/4)*star U‖ ≤ CA*CB*CP*‖star U‖ := by
    apply (norm_mul_le _ _).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply (norm_mul_le _ _).trans
    apply mul_le_mul ((norm_mul_le _ _).trans
      (mul_le_mul hAr hBr (norm_nonneg _) hCA)) hPr (norm_nonneg _) (mul_nonneg hCA hCB)
  exact (tr.le_opNorm _).trans (mul_le_mul_of_nonneg_left ht (norm_nonneg tr))

end RefinedBMV
