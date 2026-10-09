import RefinedBMV.TraceMoment
import RefinedBMV.MomentInterpolation

namespace RefinedBMV
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 700000

theorem complexPower_isUnit {d} (A : Mat d) (z : ℂ) : IsUnit (complexPower A z) := by
  let : NormedAlgebra ℚ (Mat d) := NormedAlgebra.restrictScalars ℚ ℝ (Mat d)
  exact NormedSpace.isUnit_exp _

theorem hsSquared_left_unitary {d} (U M : Mat d) (hU : U ∈ unitary (Mat d)) :
    hsSquared (U*M) = hsSquared M := by
  simpa only [traceMoment,pow_one,hsSquared,Matrix.star_eq_conjTranspose] using traceMoment_left_unitary 1 U M hU

noncomputable def altDualPath {d} (H P U V : Mat d) (N q : ℕ) (z : ℂ) : ℂ :=
  (U*complexPower H ((q : ℂ)*z)*complexPower P ((N : ℂ)*(1-z/2))*V).trace

theorem altDualPath_entire {d} (H P U V : Mat d) (N q : ℕ) :
    Differentiable ℂ (altDualPath H P U V N q) := by
  let tr : Mat d →L[ℂ] ℂ := (Matrix.traceLinearMap (Fin d) ℂ ℂ).toContinuousLinearMap
  have hh : Differentiable ℂ (fun z : ℂ => (q : ℂ)*z) := by fun_prop
  have hp : Differentiable ℂ (fun z : ℂ => (N : ℂ)*(1-z/2)) := by fun_prop
  exact tr.differentiable.comp ((((complexPower_differentiable H).comp hh).const_mul U |>.mul
    ((complexPower_differentiable P).comp hp)).mul_const V)

theorem altDualPath_left {d} (H P U V : Mat d) (N q : ℕ) (hP : P.PosDef)
    (hU : U ∈ unitary (Mat d)) (hV : V ∈ unitary (Mat d)) (t : ℝ) :
    ‖altDualPath H P U V N q ((t : ℂ)*Complex.I)‖ ≤ reTrace (P^N) := by
  let v : ℂ := (t : ℂ)*Complex.I
  let uh := complexPower H ((q : ℂ)*v)
  let up := complexPower P (-(N : ℂ)*v/2)
  have huh : uh ∈ unitary (Mat d) := complexPower_unitary_of_re_zero H _ (by simp [v])
  have hup : up ∈ unitary (Mat d) := complexPower_unitary_of_re_zero P _ (by simp [v])
  have hp : complexPower P ((N : ℂ)*(1-v/2)) = P^N*up := by
    rw [← complexPower_nat P hP N,← complexPower_add]
    congr 1
    ring
  have ht : altDualPath H P U V N q v = (P^N*(up*V*U*uh)).trace := by
    rw [altDualPath,hp]
    change (U*uh*(P^N*up)*V).trace = _
    have he : U*uh*(P^N*up)*V = (U*uh)*(P^N*up*V) := by simp only [mul_assoc]
    rw [he,Matrix.trace_mul_comm]
    simp only [mul_assoc]
  rw [ht]
  exact positive_unitary_trace_bound _ _ (hP.posSemidef.pow N)
    ((unitary (Mat d)).mul_mem ((unitary (Mat d)).mul_mem
      ((unitary (Mat d)).mul_mem hup hV) hU) huh)

theorem altDualPath_right {d} (H P U V : Mat d) (N q : ℕ) (hH : H.PosDef) (hP : P.PosDef)
    (hU : U ∈ unitary (Mat d)) (hV : V ∈ unitary (Mat d)) (t : ℝ) :
    ‖altDualPath H P U V N q (1+(t : ℂ)*Complex.I)‖^2 ≤ reTrace (H^(2*q))*reTrace (P^N) := by
  let v : ℂ := (t : ℂ)*Complex.I
  let uh := complexPower H ((q : ℂ)*v)
  let up := complexPower P (-(N : ℂ)*v/2)
  let G := complexPower P (((N : ℝ)/2 : ℝ) : ℂ)
  have huh : uh ∈ unitary (Mat d) := complexPower_unitary_of_re_zero H _ (by simp [v])
  have hup : up ∈ unitary (Mat d) := complexPower_unitary_of_re_zero P _ (by simp [v])
  have hh : complexPower H ((q : ℂ)*(1+v)) = H^q*uh := by
    rw [← complexPower_nat H hH q,← complexPower_add]
    congr 1
    ring
  have hp : complexPower P ((N : ℂ)*(1-(1+v)/2)) = G*up := by
    rw [← complexPower_add]
    congr 1
    push_cast
    ring
  have ht : altDualPath H P U V N q (1+v) = ((U*H^q*uh)*(G*up*V)).trace := by
    rw [altDualPath,hh,hp]
    simp only [mul_assoc]
  have he : hsSquared (H^q) = reTrace (H^(2*q)) := by
    rw [hsSquared,Matrix.star_eq_conjTranspose,(hH.isHermitian.pow q).eq,← pow_add,two_mul]
  have h := trace_cauchy_schwarz (U*H^q*uh) (G*up*V)
  rw [hsSquared_right_unitary _ _ huh,hsSquared_left_unitary _ _ hU,
    hsSquared_right_unitary _ _ hV,hsSquared_right_unitary _ _ hup,he,hsSquared_root P hP N] at h
  rw [ht]
  exact h

theorem altDualPath_bounded {d} (H P U V : Mat d) (N q : ℕ) :
    ∃ K : ℝ, ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → ‖altDualPath H P U V N q z‖ ≤ K := by
  obtain ⟨CH,hCH,bH⟩ := complexPower_bounded_strip H 0 q
  obtain ⟨CP,hCP,bP⟩ := complexPower_bounded_strip P ((N : ℝ)/2) N
  let tr : Mat d →L[ℂ] ℂ := (Matrix.traceLinearMap (Fin d) ℂ ℂ).toContinuousLinearMap
  refine ⟨‖tr‖*(‖U‖*CH*CP*‖V‖),?_⟩
  intro z hlo hhi
  have hrH : ((q : ℂ)*z).re = (q : ℝ)*z.re := by simp
  have hrP : ((N : ℂ)*(1-z/2)).re = (N : ℝ)*(1-z.re/2) := by simp
  have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hHr := bH ((q : ℂ)*z) (by rw [hrH]; positivity) (by rw [hrH]; nlinarith)
  have hPr := bP ((N : ℂ)*(1-z/2)) (by rw [hrP]; nlinarith) (by rw [hrP]; nlinarith)
  have ht : ‖U*complexPower H ((q : ℂ)*z)*complexPower P ((N : ℂ)*(1-z/2))*V‖ ≤
      ‖U‖*CH*CP*‖V‖ := by
    apply (norm_mul_le _ _).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply (norm_mul_le _ _).trans
    apply mul_le_mul ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hHr (norm_nonneg _)))
      hPr (norm_nonneg _) (mul_nonneg (norm_nonneg _) hCH)
  exact (tr.le_opNorm _).trans (mul_le_mul_of_nonneg_left ht (norm_nonneg tr))

/-- Dual Schatten Holder for every positive integer q, with arbitrary positive weight moment N. -/
theorem alt_weighted_holder {d} (hdim : 0 < d) (M P V : Mat d) (N q : ℕ)
    (hq : 0 < q) (hM : IsUnit M) (hP : P.PosDef) (hV : V ∈ unitary (Mat d)) :
    ‖(M*complexPower P (((N : ℝ)*(1-1/(2*q)) : ℝ) : ℂ)*V).trace‖^(2*q) ≤
      traceMoment q M*(reTrace (P^N))^(2*q-1) := by
  obtain ⟨U,H,hU,hH,hUH,hHH⟩ := invertible_polar M hM
  have hS : 0 < reTrace (P^N) := by
    let : NeZero d := ⟨by omega⟩
    exact (RCLike.pos_iff.mp (posDef_nat_pow P hP N).trace_pos).1
  have hT : 0 ≤ reTrace (H^(2*q)) := (RCLike.nonneg_iff.mp (hH.posSemidef.pow (2*q)).trace_nonneg).1
  have hl : ∀ z : ℂ, z.re = 0 → ‖altDualPath H P U V N q z‖ ≤ reTrace (P^N) := by
    intro z hz
    have he : z = (z.im : ℂ)*Complex.I := by apply Complex.ext <;> simp [hz]
    rw [he]
    exact altDualPath_left H P U V N q hP hU hV z.im
  have hr : ∀ z : ℂ, z.re = 1 → ‖altDualPath H P U V N q z‖^2 ≤ reTrace (H^(2*q))*reTrace (P^N) := by
    intro z hz
    have he : z = 1+(z.im : ℂ)*Complex.I := by apply Complex.ext <;> simp [hz]
    rw [he]
    exact altDualPath_right H P U V N q hH hP hU hV z.im
  have hi := dual_moment_interpolation (altDualPath H P U V N q) (reTrace (P^N))
    (reTrace (H^(2*q))) q hS hT hq (altDualPath_entire H P U V N q)
    (altDualPath_bounded H P U V N q) hl hr
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have he : altDualPath H P U V N q ((1/(q : ℝ) : ℝ) : ℂ) =
      (M*complexPower P (((N : ℝ)*(1-1/(2*q)) : ℝ) : ℂ)*V).trace := by
    unfold altDualPath
    push_cast
    rw [mul_one_div_cancel hqC,complexPower_one H hH,← hUH]
    have hp : (N : ℂ)*(1-(1/(q : ℂ))/2) = (N : ℂ)*(1-1/(2*(q : ℂ))) := by ring
    rw [hp]
  rw [he] at hi
  rw [traceMoment_polar q M H hHH]
  exact hi

end RefinedBMV
