import RefinedBMV.StripDiskPoint
import RefinedBMV.EvenDisk

namespace RefinedBMV
open Filter Topology Metric Set
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 500000

/-- The unrestricted positive definite one-point ratio estimate (7.12).
The witness is exactly the normalized midpoint C/sqrt(D*C). -/
theorem cubicStripTrace_point_ratio_bound {d} (hdim : 0 < d) (X Y : Mat d)
    (hX : X.PosDef) (hY : Y.PosDef) :
    ∃ a : ℝ, 0 ≤ a ∧ a ≤ 1 ∧
      (cubicStripTrace X Y (1/2)).re = reTrace (X*Y)*a^2 ∧
      reTrace (X*Y)*a*(3*a-1)/(3-a) ≤ (cubicStripTrace X Y (2/3)).re := by
  let D := reTrace (X*Y)
  let C := (cubicStripTrace X Y (1/2)).re
  let R := Real.sqrt (D*C)
  let a := C/R
  have hC0 : 0 < C := by
    dsimp [C]
    rw [cubic_midpoint_eq_sqrt X Y hX hY]
    exact cubic_center_pos hdim X Y hX hY
  have hCD : C ≤ D := by
    dsimp [C,D]
    rw [cubic_midpoint_eq_sqrt X Y hX hY]
    exact cubic_center_le_endpoint X Y hX.posSemidef hY.posSemidef
  have hD0 : 0 < D := hC0.trans_le hCD
  have hR0 : 0 < R := Real.sqrt_pos.mpr (mul_pos hD0 hC0)
  have hR2 : R^2 = D*C := Real.sq_sqrt (mul_nonneg hD0.le hC0.le)
  have ha0 : 0 ≤ a := (div_pos hC0 hR0).le
  have ha1 : a ≤ 1 := by
    apply (div_le_one₀ hR0).mpr
    apply (sq_le_sq₀ hC0.le hR0.le).mp
    rw [hR2]
    nlinarith only [mul_le_mul_of_nonneg_right hCD hC0.le]
  have hDa : D*a = R := by
    dsimp [a]
    rw [← mul_div_assoc]
    apply (div_eq_iff hR0.ne').mpr
    nlinarith only [hR2]
  have hCa : C = D*a^2 := by
    have hCa' : C = a*R := by dsimp [a]; field_simp
    rw [← hDa] at hCa'
    nlinarith only [hCa']
  let h : ℂ → ℂ := fun w => cubicStripTrace X Y (stripDiskInverse w)/(R : ℂ)
  have hhd : DifferentiableOn ℂ h (ball 0 1) :=
    ((cubicStripTrace_entire X Y).comp_differentiableOn stripDiskInverse_differentiable).div_const _
  have hhe : ∀ w ∈ ball (0 : ℂ) 1, h (-w) = h w := by
    intro w hw
    have hwn : ‖w‖ < 1 := by simpa [mem_ball,dist_eq_norm] using hw
    dsimp [h]
    rw [stripDiskInverse_neg w hwn,cubicStripTrace_center_symmetry]
  have hhb : ∀ w ∈ ball (0 : ℂ) 1, ‖h w‖ ≤ 1 := by
    intro w hw
    have hwn : ‖w‖ < 1 := by simpa [mem_ball,dist_eq_norm] using hw
    have hr := stripDiskInverse_maps_strip w hwn
    have hb := cubicStripTrace_sharp_strip X Y hX hY (stripDiskInverse w) hr.1.le hr.2.le
    change ‖cubicStripTrace X Y (stripDiskInverse w)/(R : ℂ)‖ ≤ 1
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hR0,div_le_one₀ hR0]
    exact hb
  have hfC : cubicStripTrace X Y (1/2) = (C : ℂ) := by
    apply Complex.ext
    · rfl
    · rw [cubic_midpoint_eq_sqrt X Y hX hY,cubic_center_trace_real,Complex.ofReal_im]
  have hh0 : h 0 = (a : ℂ) := by
    dsimp [h,a]
    rw [stripDiskInverse_zero,hfC,Complex.ofReal_div]
  have hs := even_disk_point_lower h a ha0 ha1 hhd hhe hhb hh0 cubicDiskPoint cubicDiskPoint_norm_sq
  have hre : (h cubicDiskPoint).re = (cubicStripTrace X Y (2/3)).re/R := by
    simp only [h,stripDiskInverse_cubic_point,Complex.div_re,Complex.ofReal_re,
      Complex.ofReal_im,Complex.normSq_ofReal,mul_zero]
    field_simp
    ring
  rw [hre] at hs
  have hfinal := (le_div_iff₀ hR0).mp hs
  refine ⟨a,ha0,ha1,hCa,?_⟩
  change D*a*(3*a-1)/(3-a) ≤ _
  rw [hDa]
  convert hfinal using 1
  ring

/-- The analytic joint lower comparison of endpoint, mixed trace and midpoint. -/
theorem cubicStripTrace_joint_estimate {d} (hdim : 0 < d) (X Y : Mat d)
    (hX : X.PosDef) (hY : Y.PosDef) :
    3*(cubicStripTrace X Y (1/2)).re ≤
      reTrace (X*Y)+2*(cubicStripTrace X Y (2/3)).re := by
  obtain ⟨a,ha0,ha1,hCa,hW⟩ := cubicStripTrace_point_ratio_bound hdim X Y hX hY
  have hc : 0 ≤ (cubicStripTrace X Y (1/2)).re := by
    rw [cubic_midpoint_eq_sqrt X Y hX hY]
    exact (cubic_center_pos hdim X Y hX hY).le
  have hD : 0 ≤ reTrace (X*Y) := by
    have h := cubic_center_le_endpoint X Y hX.posSemidef hY.posSemidef
    unfold reTrace at h
    rw [← cubic_midpoint_eq_sqrt X Y hX hY] at h
    exact hc.trans h
  exact (cubic_joint_of_ratio_bound _ _ _ a hD ha0 ha1 hCa hW).2

end RefinedBMV
