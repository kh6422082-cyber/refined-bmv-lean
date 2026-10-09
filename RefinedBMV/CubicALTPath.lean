import RefinedBMV.PolarTrace

namespace RefinedBMV
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 600000

/-- The dual trace used to interpolate the cubic ALT instance. -/
noncomputable def cubicALTPath {d} (A B P U : Mat d) (z : ℂ) : ℂ :=
  (complexPower A (3*z/4)*complexPower B (3*z/4)*
    complexPower P (6-3*z/2)*star U).trace

theorem complexPower_unitary_of_re_zero {d} (A : Mat d) (z : ℂ) (hz : z.re = 0) :
    complexPower A z ∈ unitary (Mat d) := by
  have he : z = (z.im : ℂ)*Complex.I := by apply Complex.ext <;> simp [hz]
  rw [he]
  exact complexPower_imaginary_unitary A z.im

theorem cubicALTPath_entire {d} (A B P U : Mat d) : Differentiable ℂ (cubicALTPath A B P U) := by
  let tr : Mat d →L[ℂ] ℂ := (Matrix.traceLinearMap (Fin d) ℂ ℂ).toContinuousLinearMap
  have hz : Differentiable ℂ (fun z : ℂ => 3*z/4) := by fun_prop
  have hpz : Differentiable ℂ (fun z : ℂ => 6-3*z/2) := by fun_prop
  have ha := (complexPower_differentiable A).comp hz
  have hb := (complexPower_differentiable B).comp hz
  have hp := (complexPower_differentiable P).comp hpz
  exact tr.differentiable.comp (((ha.mul hb).mul hp).mul_const (star U))

theorem cubicALTPath_left_bound {d} (A B P U : Mat d) (hP : P.PosDef)
    (hU : U ∈ unitary (Mat d)) (t : ℝ) :
    ‖cubicALTPath A B P U ((t : ℂ)*Complex.I)‖ ≤ reTrace (P^6) := by
  let v : ℂ := (t : ℂ)*Complex.I
  let ua := complexPower A (3*v/4)
  let ub := complexPower B (3*v/4)
  let up := complexPower P (-3*v/2)
  have hua : ua ∈ unitary (Mat d) := complexPower_unitary_of_re_zero A _ (by simp [v])
  have hub : ub ∈ unitary (Mat d) := complexPower_unitary_of_re_zero B _ (by simp [v])
  have hup : up ∈ unitary (Mat d) := complexPower_unitary_of_re_zero P _ (by simp [v])
  have he : complexPower P (6-3*v/2) = P^6*up := by
    rw [← complexPower_nat P hP 6,← complexPower_add]
    congr 1
    ring
  have htrace : cubicALTPath A B P U v = (P^6*(up*star U*ua*ub)).trace := by
    rw [cubicALTPath,he]
    change (ua*ub*(P^6*up)*star U).trace = _
    have hr : ua*ub*(P^6*up)*star U = (ua*ub)*(P^6*up*star U) := by noncomm_ring
    rw [hr,Matrix.trace_mul_comm]
    simp only [mul_assoc]
  rw [htrace]
  exact positive_unitary_trace_bound _ _ (hP.posSemidef.pow 6)
    ((unitary (Mat d)).mul_mem ((unitary (Mat d)).mul_mem
      ((unitary (Mat d)).mul_mem hup (Unitary.star_mem hU)) hua) hub)

theorem hsFourth_three_halves {d} (P : Mat d) (hP : P.PosDef) :
    hsFourth (complexPower P (3/2)) = reTrace (P^6) := by
  have hs : star (complexPower P (3/2)) = complexPower P (3/2) := by
    rw [complexPower_star]
    norm_num
  rw [hsFourth,hs,pow_two,← complexPower_add,← complexPower_add]
  norm_num
  have hn := complexPower_nat P hP 6
  norm_num at hn
  rw [hn]

theorem hsSquared_cube {d} (P : Mat d) (hP : P.IsHermitian) :
    hsSquared (P^3) = reTrace (P^6) := by
  rw [hsSquared,Matrix.star_eq_conjTranspose,(hP.pow 3).eq,← pow_add]

/-- The right boundary uses only the already proved 4/4/2 trace Holder inequality. -/
theorem cubicALTPath_right_fourth_bound {d} (A B P U : Mat d) (hP : P.PosDef)
    (hU : U ∈ unitary (Mat d)) (t : ℝ) :
    ‖cubicALTPath A B P U (1+(t : ℂ)*Complex.I)‖^4 ≤
      hsFourth (complexPower A (3/4)*complexPower B (3/4))*(reTrace (P^6))^3 := by
  let v : ℂ := (t : ℂ)*Complex.I
  let ua := complexPower A (3*v/4)
  let ub := complexPower B (3*v/4)
  let up := complexPower P (-3*v/2)
  let M := complexPower A (3/4)*complexPower B (3/4)
  let N := complexPower P (3/2)
  have hua : ua ∈ unitary (Mat d) := complexPower_unitary_of_re_zero A _ (by simp [v])
  have hub : ub ∈ unitary (Mat d) := complexPower_unitary_of_re_zero B _ (by simp [v])
  have hup : up ∈ unitary (Mat d) := complexPower_unitary_of_re_zero P _ (by simp [v])
  have ha : complexPower A (3*(1+v)/4) = ua*complexPower A (3/4) := by
    rw [← complexPower_add]
    congr 1
    ring
  have hb : complexPower B (3*(1+v)/4) = complexPower B (3/4)*ub := by
    rw [← complexPower_add]
    congr 1
    ring
  have hp : complexPower P (6-3*(1+v)/2) = N*(P^3*up) := by
    rw [← complexPower_nat P hP 3]
    change complexPower P (6-3*(1+v)/2) =
      complexPower P (3/2)*(complexPower P 3*complexPower P (-3*v/2))
    rw [← complexPower_add,← complexPower_add]
    congr 1
    ring
  have ht : cubicALTPath A B P U (1+v) = ((ua*M*ub)*N*(P^3*up*star U)).trace := by
    rw [cubicALTPath,ha,hb,hp]
    dsimp only [M]
    simp only [mul_assoc]
  have h := trace_holder_442 (ua*M*ub) N (P^3*up*star U)
  rw [hsFourth_right_unitary _ _ hub,hsFourth_left_unitary _ _ hua,
    hsSquared_right_unitary _ _ (Unitary.star_mem hU),hsSquared_right_unitary _ _ hup,
    hsFourth_three_halves P hP,hsSquared_cube P hP.isHermitian] at h
  rw [ht]
  convert h using 1
  ring

end RefinedBMV
