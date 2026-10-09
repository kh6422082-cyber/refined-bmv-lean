import RefinedBMV.TraceHolder
import Mathlib.Analysis.Complex.Hadamard

namespace RefinedBMV
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 700000

theorem reTrace_unitary_reverse_conj_pow {d} (U M : Mat d) (hU : U ∈ unitary (Mat d))
    (k : ℕ) : reTrace ((star U*M*U)^k) = reTrace (M^k) := by
  let W : Matrix.unitaryGroup (Fin d) ℂ := ⟨star U, Unitary.star_mem hU⟩
  have h := unitary_trace_conj_pow W M k
  simpa only [W, star_star] using h

theorem hsFourth_right_unitary {d} (M U : Mat d) (hU : U ∈ unitary (Mat d)) :
    hsFourth (M*U) = hsFourth M := by
  have he : star (M*U)*(M*U) = star U*(star M*M)*U := by
    rw [star_mul]
    simp only [mul_assoc]
  rw [hsFourth,he]
  exact reTrace_unitary_reverse_conj_pow U (star M*M) hU 2

theorem hsSquared_right_unitary {d} (M U : Mat d) (hU : U ∈ unitary (Mat d)) :
    hsSquared (M*U) = hsSquared M := by
  have he : star (M*U)*(M*U) = star U*(star M*M)*U := by
    rw [star_mul]
    simp only [mul_assoc]
  have h := reTrace_unitary_reverse_conj_pow U (star M*M) hU 1
  simpa only [pow_one, hsSquared, he] using h

theorem complexPower_real_hermitian {d} (A : Mat d) (r : ℝ) :
    (complexPower A (r : ℂ)).IsHermitian := by
  change star (complexPower A (r : ℂ)) = _
  rw [complexPower_star]
  simp only [Complex.star_def, Complex.conj_ofReal]

theorem complexPower_one {d} (A : Mat d) (hA : A.PosDef) : complexPower A 1 = A := by
  unfold complexPower
  rw [one_smul]
  exact CFC.exp_log A hA.isStrictlyPositive

theorem cubic_midpoint_eq_sqrt {d} (X Y : Mat d) (hX : X.PosDef) (hY : Y.PosDef) :
    cubicStripTrace X Y (1/2) = ((CFC.sqrt X*CFC.sqrt Y)^2).trace := by
  rw [cubicStripTrace_midpoint_real X Y hX hY]
  have hx := CFC.sqrt_eq_rpow (a := X)
  have hy := CFC.sqrt_eq_rpow (a := Y)
  change CFC.sqrt X = CFC.rpow X (1/2) at hx
  change CFC.sqrt Y = CFC.rpow Y (1/2) at hy
  rw [← hx, ← hy]

theorem cubic_quarter_hsFourth {d} (X Y : Mat d) :
    hsFourth (complexPower Y (1/4)*complexPower X (1/4)) =
      (cubicStripTrace X Y (1/2)).re := by
  let x := complexPower X (1/4)
  let y := complexPower Y (1/4)
  have hx : star x = x := by simpa [x, Matrix.star_eq_conjTranspose] using (complexPower_real_hermitian X (1/4)).eq
  have hy : star y = y := by simpa [y, Matrix.star_eq_conjTranspose] using (complexPower_real_hermitian Y (1/4)).eq
  have hx2 : x*x = complexPower X (1/2) := by
    rw [← complexPower_add]
    norm_num
  have hy2 : y*y = complexPower Y (1/2) := by
    rw [← complexPower_add]
    norm_num
  change hsFourth (y*x) = _
  rw [hsFourth, star_mul,hx,hy]
  have he : (x*y*(y*x))^2 = x*((y*y)*(x*x)*(y*y))*x := by noncomm_ring
  rw [he, reTrace_cycle (x*((y*y)*(x*x)*(y*y))) x]
  have ht : x*(x*((y*y)*(x*x)*(y*y))) = (x*x*(y*y))^2 := by noncomm_ring
  rw [ht,hx2,hy2,cubicStripTrace_midpoint]
  rfl

theorem cubic_half_hsSquared {d} (X Y : Mat d) (hX : X.PosDef) (hY : Y.PosDef) :
    hsSquared (complexPower X (1/2)*complexPower Y (1/2)) = reTrace (X*Y) := by
  let x := complexPower X (1/2)
  let y := complexPower Y (1/2)
  have hx : star x = x := by simpa [x, Matrix.star_eq_conjTranspose] using (complexPower_real_hermitian X (1/2)).eq
  have hy : star y = y := by simpa [y, Matrix.star_eq_conjTranspose] using (complexPower_real_hermitian Y (1/2)).eq
  have hx2 : x*x = X := by
    rw [← complexPower_add]
    norm_num
    exact complexPower_one X hX
  have hy2 : y*y = Y := by
    rw [← complexPower_add]
    norm_num
    exact complexPower_one Y hY
  change hsSquared (x*y) = _
  rw [hsSquared,star_mul,hx,hy]
  have he : y*x*(x*y) = y*(x*x)*y := by noncomm_ring
  rw [he,hx2]
  calc
    reTrace (y*X*y) = reTrace (X*(y*y)) := by
      simpa only [mul_assoc] using reTrace_cycle y (X*y)
    _ = reTrace (X*Y) := by rw [hy2]

/-- The exact center-dependent boundary modulus (7.7). -/
theorem cubicStripTrace_left_bound {d} (X Y : Mat d) (hX : X.PosDef) (hY : Y.PosDef) (t : ℝ) :
    ‖cubicStripTrace X Y (1/4+(t : ℂ)*Complex.I)‖ ≤
      Real.sqrt (reTrace (X*Y)*(cubicStripTrace X Y (1/2)).re) := by
  let P := complexPower Y (1/4)*complexPower X (1/4)
  let Q := complexPower X (1/2)*complexPower Y (1/2)
  let ux := complexPower X ((t : ℂ)*Complex.I)
  let uy := complexPower Y ((t : ℂ)*Complex.I)
  let vx := complexPower X (-((t : ℂ)*Complex.I))
  let vy := complexPower Y (-((t : ℂ)*Complex.I))
  have hux := complexPower_imaginary_unitary X t
  have huy := complexPower_imaginary_unitary Y t
  have hvx : vx ∈ unitary (Mat d) := by
    have h := complexPower_imaginary_unitary X (-t)
    simpa only [Complex.ofReal_neg, neg_mul] using h
  have hvy : vy ∈ unitary (Mat d) := by
    have h := complexPower_imaginary_unitary Y (-t)
    simpa only [Complex.ofReal_neg, neg_mul] using h
  have h := trace_holder_442 (P*ux*uy) (P*vx) (Q*vy)
  rw [hsFourth_right_unitary _ _ huy,hsFourth_right_unitary _ _ hux,
    hsFourth_right_unitary _ _ hvx,hsSquared_right_unitary _ _ hvy] at h
  have hc : hsFourth P = (cubicStripTrace X Y (1/2)).re := cubic_quarter_hsFourth X Y
  have hd : hsSquared Q = reTrace (X*Y) := cubic_half_hsSquared X Y hX hY
  rw [hc,hd] at h
  have hf := cubicStripTrace_boundary_factorization X Y t
  dsimp only at hf
  change cubicStripTrace X Y (1/4+(t : ℂ)*Complex.I) = ((P*ux*uy)*(P*vx)*(Q*vy)).trace at hf
  rw [← hf] at h
  have hc0 : 0 ≤ (cubicStripTrace X Y (1/2)).re := hc ▸ hsFourth_nonneg P
  have hd0 : 0 ≤ reTrace (X*Y) := hd ▸ hsSquared_nonneg Q
  have hprod := mul_nonneg hd0 hc0
  apply Real.le_sqrt_of_sq_le
  apply (sq_le_sq₀ (sq_nonneg _) hprod).mp
  convert h using 1 <;> ring

/-- The sharp modulus throughout the closed strip, (7.8). -/
theorem cubicStripTrace_sharp_strip {d} (X Y : Mat d) (hX : X.PosDef) (hY : Y.PosDef)
    (z : ℂ) (hzlo : (1/4 : ℝ) ≤ z.re) (hzhi : z.re ≤ (3/4 : ℝ)) :
    ‖cubicStripTrace X Y z‖ ≤ Real.sqrt (reTrace (X*Y)*(cubicStripTrace X Y (1/2)).re) := by
  let R := Real.sqrt (reTrace (X*Y)*(cubicStripTrace X Y (1/2)).re)
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hb0 : ∀ w : ℂ, w.re = (1/4 : ℝ) → ‖cubicStripTrace X Y w‖ ≤ R := by
    intro w hw
    have he : w = 1/4+(w.im : ℂ)*Complex.I := by
      apply Complex.ext <;> simp [hw]
    rw [he]
    exact cubicStripTrace_left_bound X Y hX hY w.im
  have hb1 : ∀ w : ℂ, w.re = (3/4 : ℝ) → ‖cubicStripTrace X Y w‖ ≤ R := by
    intro w hw
    rw [← cubicStripTrace_center_symmetry X Y w]
    apply hb0
    simp only [Complex.sub_re,Complex.one_re,hw]
    norm_num
  obtain ⟨C,hC⟩ := cubicStripTrace_bounded_strip X Y (1/4) (3/4)
  have hbounded : BddAbove ((norm ∘ cubicStripTrace X Y) ''
      Complex.HadamardThreeLines.verticalClosedStrip (1/4) (3/4)) := by
    refine ⟨C, ?_⟩
    rintro _ ⟨w,hw,rfl⟩
    exact hC w hw.1 hw.2
  have hs := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
    (f := cubicStripTrace X Y) (a := R) (b := R) (l := (1/4 : ℝ)) (u := (3/4 : ℝ))
    (by norm_num) ⟨hzlo,hzhi⟩ (cubicStripTrace_entire X Y).diffContOnCl hbounded
    (fun w hw => hb0 w hw) (fun w hw => hb1 w hw)
  have he (a : ℝ) : R^(1-a)*R^a = R := by
    rw [← Real.rpow_add' hR (by ring_nf; norm_num), sub_add_cancel, Real.rpow_one]
  rw [he] at hs
  exact hs

end RefinedBMV
