import RefinedBMV.CubicStrip
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace RefinedBMV
open Filter Topology Metric Set
set_option maxHeartbeats 400000

noncomputable def diskCayley (w : ℂ) : ℂ := (1+Complex.I*w)/(1-Complex.I*w)
noncomputable def stripDiskCenter (w : ℂ) : ℂ :=
  -Complex.I*Complex.log (diskCayley w)/((2*Real.pi : ℝ) : ℂ)
noncomputable def stripDiskInverse (w : ℂ) : ℂ := 1/2+stripDiskCenter w

theorem diskCayley_den_ne (w : ℂ) (hw : ‖w‖ < 1) : 1-Complex.I*w ≠ 0 := by
  intro he
  have h : Complex.I*w = 1 := by linear_combination -he
  have hn := congrArg norm h
  simp only [norm_mul,Complex.norm_I,one_mul,norm_one] at hn
  linarith

theorem diskCayley_re (w : ℂ) :
    (diskCayley w).re = (1-‖w‖^2)/‖1-Complex.I*w‖^2 := by
  simp only [diskCayley,Complex.div_re,Complex.sq_norm,Complex.normSq_apply,
    Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im,
    Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
    Complex.one_re,Complex.one_im,zero_mul,one_mul,zero_add,zero_sub]
  ring

theorem diskCayley_re_pos (w : ℂ) (hw : ‖w‖ < 1) : 0 < (diskCayley w).re := by
  rw [diskCayley_re]
  apply div_pos
  · nlinarith [norm_nonneg w]
  · exact sq_pos_of_pos (norm_pos_iff.mpr (diskCayley_den_ne w hw))

theorem diskCayley_slitPlane (w : ℂ) (hw : ‖w‖ < 1) : diskCayley w ∈ Complex.slitPlane := by
  exact Or.inl (diskCayley_re_pos w hw)

theorem stripDiskInverse_differentiable :
    DifferentiableOn ℂ stripDiskInverse (ball 0 1) := by
  have hd : DifferentiableOn ℂ diskCayley (ball 0 1) :=
    ((differentiableOn_const _).add ((differentiableOn_const _).mul differentiableOn_id)).div
      ((differentiableOn_const _).sub ((differentiableOn_const _).mul differentiableOn_id))
      (fun w hw => diskCayley_den_ne w (by simpa [mem_ball,dist_eq_norm] using hw))
  have hl := hd.clog (fun w hw => diskCayley_slitPlane w (by simpa [mem_ball,dist_eq_norm] using hw))
  exact (differentiableOn_const _).add (((differentiableOn_const _).mul hl).div_const _)

theorem stripDiskCenter_re (w : ℂ) :
    (stripDiskCenter w).re = (diskCayley w).arg/(2*Real.pi) := by
  simp only [stripDiskCenter,Complex.div_re,Complex.mul_re,Complex.mul_im,
    Complex.neg_re,Complex.neg_im,Complex.I_re,Complex.I_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.normSq_ofReal,Complex.log_im]
  have hp : Real.pi ≠ 0 := Real.pi_pos.ne'
  field_simp
  ring

theorem stripDiskInverse_maps_strip (w : ℂ) (hw : ‖w‖ < 1) :
    (1/4 : ℝ) < (stripDiskInverse w).re ∧ (stripDiskInverse w).re < (3/4 : ℝ) := by
  have ha := (Complex.abs_arg_lt_pi_div_two_iff).mpr (Or.inl (diskCayley_re_pos w hw))
  rw [abs_lt] at ha
  have hp : 0 < 2*Real.pi := by positivity
  have hlo : -(1/4 : ℝ) < (diskCayley w).arg/(2*Real.pi) := by
    apply (lt_div_iff₀ hp).mpr
    linarith [ha.1]
  have hhi : (diskCayley w).arg/(2*Real.pi) < (1/4 : ℝ) := by
    apply (div_lt_iff₀ hp).mpr
    linarith [ha.2]
  simp only [stripDiskInverse,Complex.add_re,stripDiskCenter_re]
  norm_num
  constructor <;> linarith

theorem diskCayley_neg (w : ℂ) : diskCayley (-w) = (diskCayley w)⁻¹ := by
  simp only [diskCayley,mul_neg,sub_neg_eq_add,inv_div]
  rw [← sub_eq_add_neg]

theorem stripDiskCenter_odd (w : ℂ) (hw : ‖w‖ < 1) :
    stripDiskCenter (-w) = -stripDiskCenter w := by
  rw [stripDiskCenter,diskCayley_neg,Complex.log_inv _
    (Complex.slitPlane_arg_ne_pi (diskCayley_slitPlane w hw))]
  simp only [stripDiskCenter,mul_neg,neg_div]

theorem stripDiskInverse_neg (w : ℂ) (hw : ‖w‖ < 1) :
    stripDiskInverse (-w) = 1-stripDiskInverse w := by
  rw [stripDiskInverse,stripDiskCenter_odd w hw,stripDiskInverse]
  ring

theorem stripDiskInverse_zero : stripDiskInverse 0 = (1/2 : ℂ) := by
  simp [stripDiskInverse,stripDiskCenter,diskCayley]

end RefinedBMV
