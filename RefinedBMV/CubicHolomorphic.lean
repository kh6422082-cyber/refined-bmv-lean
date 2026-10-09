import RefinedBMV.Commuting
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Normed.Group.Bounded

namespace RefinedBMV
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 600000

/-- Complex matrix powers via the matrix logarithm. Paper applications require positive inputs. -/
noncomputable def complexPower {d} (A : Mat d) (z : ℂ) : Mat d :=
  NormedSpace.exp (z • CFC.log A)

/-- The complete complex trace in (7.3). -/
noncomputable def cubicStripTrace {d} (X Y : Mat d) (z : ℂ) : ℂ :=
  (complexPower X z * complexPower Y z * complexPower X (1-z) *
    complexPower Y (1-z)).trace

theorem complexPower_differentiable {d} (A : Mat d) :
    Differentiable ℂ (complexPower A) := by
  have he : Differentiable ℂ (NormedSpace.exp : Mat d → Mat d) :=
    fun M => (NormedSpace.exp_analytic (𝕂 := ℂ) M).differentiableAt
  exact he.comp (differentiable_id.smul_const (CFC.log A))

theorem cubicStripTrace_entire {d} (X Y : Mat d) :
    Differentiable ℂ (cubicStripTrace X Y) := by
  let tr : Mat d →L[ℂ] ℂ := (Matrix.traceLinearMap (Fin d) ℂ ℂ).toContinuousLinearMap
  have hX := complexPower_differentiable X
  have hY := complexPower_differentiable Y
  have hsub : Differentiable ℂ (fun z : ℂ => 1-z) := differentiable_const 1 |>.sub differentiable_id
  have hp := ((hX.mul hY).mul (hX.comp hsub)).mul (hY.comp hsub)
  exact tr.differentiable.comp hp

theorem cubicStripTrace_center_symmetry {d} (X Y : Mat d) (z : ℂ) :
    cubicStripTrace X Y (1-z) = cubicStripTrace X Y z := by
  unfold cubicStripTrace
  have he : (1 : ℂ)-(1-z) = z := by ring
  rw [he]
  simpa only [mul_assoc] using Matrix.trace_mul_comm
    (complexPower X (1-z)*complexPower Y (1-z))
    (complexPower X z*complexPower Y z)

theorem cubicStripTrace_midpoint {d} (X Y : Mat d) :
    cubicStripTrace X Y (1/2) = ((complexPower X (1/2)*complexPower Y (1/2))^2).trace := by
  unfold cubicStripTrace
  have he : (1 : ℂ)-1/2 = 1/2 := by norm_num
  rw [he, pow_two]
  simp only [mul_assoc]

/-- Agreement with the positive real matrix power; this ties (7.3) to the paper's CFC powers. -/
theorem complexPower_real {d} (A : Mat d) (hA : A.PosDef) (r : ℝ) :
    complexPower A (r : ℂ) = CFC.rpow A r := by
  have hpos : IsStrictlyPositive A := hA.isUnit.isStrictlyPositive hA.posSemidef.nonneg
  have hl : ContinuousOn Real.log (spectrum ℝ A) := by
    apply ContinuousOn.log continuousOn_id
    intro x hx
    exact (hpos.spectrum_pos hx).ne'
  have hs : IsSelfAdjoint (r • CFC.log A) := (isSelfAdjoint_iff.mpr (star_trivial r)).smul .log
  have hr := CFC.rpow_eq_cfc_real (a := A) (y := r) hA.posSemidef.nonneg
  change CFC.rpow A r = cfc (fun x : ℝ => x^r) A at hr
  unfold complexPower
  have hsmul : (r : ℂ) • CFC.log A = r • CFC.log A := by
    ext i j
    simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
  rw [hsmul, ← CFC.real_exp_eq_normedSpace_exp hs, CFC.log,
    ← cfc_const_mul r Real.log A hl, ← cfc_comp' Real.exp (fun x => r*Real.log x) A
      (by fun_prop) (hl.const_mul r) hA.isHermitian.isSelfAdjoint, hr]
  apply cfc_congr
  intro x hx
  change Real.exp (r*Real.log x) = x^r
  rw [Real.rpow_def_of_pos (hpos.spectrum_pos hx), mul_comm r]

theorem cubicStripTrace_midpoint_real {d} (X Y : Mat d) (hX : X.PosDef) (hY : Y.PosDef) :
    cubicStripTrace X Y (1/2) = ((CFC.rpow X (1/2)*CFC.rpow Y (1/2))^2).trace := by
  rw [cubicStripTrace_midpoint]
  have he : (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) := by norm_num
  rw [he, complexPower_real X hX, complexPower_real Y hY]

theorem complexPower_add {d} (A : Mat d) (z w : ℂ) :
    complexPower A (z+w) = complexPower A z*complexPower A w := by
  let : NormedAlgebra ℚ (Mat d) := NormedAlgebra.restrictScalars ℚ ℝ (Mat d)
  unfold complexPower
  rw [add_smul, NormedSpace.exp_add_of_commute
    (((Commute.refl (CFC.log A)).smul_left z).smul_right w)]

theorem complexPower_imaginary_unitary {d} (A : Mat d) (t : ℝ) :
    complexPower A ((t : ℂ)*Complex.I) ∈ unitary (Mat d) := by
  let : NormedAlgebra ℚ (Mat d) := NormedAlgebra.restrictScalars ℚ ℝ (Mat d)
  have hz : (t : ℂ)*Complex.I ∈ skewAdjoint ℂ := by
    rw [skewAdjoint.mem_iff]
    simp [star_mul, mul_comm]
  exact NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
    (IsSelfAdjoint.log.smul_mem_skewAdjoint hz)

theorem complexPower_star {d} (A : Mat d) (z : ℂ) :
    star (complexPower A z) = complexPower A (star z) := by
  let : NormedAlgebra ℚ (Mat d) := NormedAlgebra.restrictScalars ℚ ℝ (Mat d)
  unfold complexPower
  rw [NormedSpace.star_exp, star_smul, IsSelfAdjoint.log.star_eq]

theorem complexPower_norm_realpart {d} (A : Mat d) (z : ℂ) :
    ‖complexPower A z‖ = ‖complexPower A (z.re : ℂ)‖ := by
  conv_lhs => rw [← Complex.re_add_im z]
  rw [complexPower_add]
  exact CStarRing.norm_mul_mem_unitary _ (complexPower_imaginary_unitary A z.im)

theorem complexPower_bounded_strip {d} (A : Mat d) (lo hi : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, lo ≤ z.re → z.re ≤ hi → ‖complexPower A z‖ ≤ C := by
  have hc : Continuous (fun r : ℝ => complexPower A (r : ℂ)) :=
    (complexPower_differentiable A).continuous.comp Complex.continuous_ofReal
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro z hlo hhi
  rw [complexPower_norm_realpart]
  exact (hC z.re ⟨hlo,hhi⟩).trans (le_max_left _ _)

theorem cubicStripTrace_bounded_strip {d} (X Y : Mat d) (lo hi : ℝ) :
    ∃ C : ℝ, ∀ z : ℂ, lo ≤ z.re → z.re ≤ hi → ‖cubicStripTrace X Y z‖ ≤ C := by
  obtain ⟨CX,hCX,bX⟩ := complexPower_bounded_strip X lo hi
  obtain ⟨CY,hCY,bY⟩ := complexPower_bounded_strip Y lo hi
  obtain ⟨DX,hDX,cX⟩ := complexPower_bounded_strip X (1-hi) (1-lo)
  obtain ⟨DY,hDY,cY⟩ := complexPower_bounded_strip Y (1-hi) (1-lo)
  let tr : Mat d →L[ℂ] ℂ := (Matrix.traceLinearMap (Fin d) ℂ ℂ).toContinuousLinearMap
  refine ⟨‖tr‖*(CX*CY*DX*DY), ?_⟩
  intro z hlo hhi
  have hzlo : 1-hi ≤ (1-z).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have hzhi : (1-z).re ≤ 1-lo := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have hp : ‖complexPower X z * complexPower Y z * complexPower X (1-z) *
      complexPower Y (1-z)‖ ≤ CX*CY*DX*DY := by
    apply (norm_mul_le _ _).trans
    apply mul_le_mul ((norm_mul_le _ _).trans
      (mul_le_mul ((norm_mul_le _ _).trans
        (mul_le_mul (bX z hlo hhi) (bY z hlo hhi) (norm_nonneg _) hCX))
        (cX (1-z) hzlo hzhi) (norm_nonneg _) (mul_nonneg hCX hCY)))
      (cY (1-z) hzlo hzhi) (norm_nonneg _) (mul_nonneg (mul_nonneg hCX hCY) hDX)
  exact (tr.le_opNorm _).trans (mul_le_mul_of_nonneg_left hp (norm_nonneg tr))

theorem complexPower_commute {d} (A : Mat d) (z w : ℂ) :
    Commute (complexPower A z) (complexPower A w) := by
  rw [commute_iff_eq, ← complexPower_add, ← complexPower_add, add_comm]

/-- The ordered boundary factorization (7.6), retaining the complete complex trace. -/
theorem cubicStripTrace_boundary_factorization {d} (X Y : Mat d) (t : ℝ) :
    let P := complexPower Y (1/4)*complexPower X (1/4)
    let Q := complexPower X (1/2)*complexPower Y (1/2)
    cubicStripTrace X Y (1/4+(t : ℂ)*Complex.I) =
      ((P*complexPower X ((t : ℂ)*Complex.I)*complexPower Y ((t : ℂ)*Complex.I))*
        (P*complexPower X (-((t : ℂ)*Complex.I)))*
        (Q*complexPower Y (-((t : ℂ)*Complex.I)))).trace := by
  dsimp only
  let v : ℂ := (t : ℂ)*Complex.I
  let x := complexPower X (1/4)
  let y := complexPower Y (1/4)
  let ix := complexPower X v
  let iy := complexPower Y v
  let mx := complexPower X (-v)
  let my := complexPower Y (-v)
  let hx := complexPower X (1/2)
  let hy := complexPower Y (1/2)
  have hX : complexPower X (1-(1/4+v)) = x*mx*hx := by
    change complexPower X (1-(1/4+v)) =
      complexPower X (1/4)*complexPower X (-v)*complexPower X (1/2)
    rw [← complexPower_add, ← complexPower_add]
    congr 1
    ring
  have hY : complexPower Y (1-(1/4+v)) = y*hy*my := by
    change complexPower Y (1-(1/4+v)) =
      complexPower Y (1/4)*complexPower Y (1/2)*complexPower Y (-v)
    rw [← complexPower_add, ← complexPower_add]
    congr 1
    ring
  have hiy : iy*y = y*iy := (complexPower_commute Y v (1/4)).eq
  have hend : hy*my*y = y*hy*my := by
    have hmy : my*y = y*my := (complexPower_commute Y (-v) (1/4)).eq
    have hhy : hy*y = y*hy := (complexPower_commute Y (1/2) (1/4)).eq
    rw [mul_assoc, hmy, ← mul_assoc, hhy]
  change cubicStripTrace X Y (1/4+v) =
    (((y*x*ix*iy)*(y*x*mx))*((hx*hy)*my)).trace
  unfold cubicStripTrace
  rw [hX, hY, complexPower_add, complexPower_add]
  change ((x*ix)*(y*iy)*(x*mx*hx)*(y*hy*my)).trace = _
  symm
  calc
    (((y*x*ix*iy)*(y*x*mx))*((hx*hy)*my)).trace =
        (y*(x*ix*iy*y*x*mx*hx*hy*my)).trace := by congr 1; noncomm_ring
    _ = ((x*ix*iy*y*x*mx*hx*hy*my)*y).trace := Matrix.trace_mul_comm _ _
    _ = ((x*ix)*(iy*y)*(x*mx*hx)*(hy*my*y)).trace := by congr 1; noncomm_ring
    _ = ((x*ix)*(y*iy)*(x*mx*hx)*(y*hy*my)).trace := by rw [hiy,hend]

end RefinedBMV
