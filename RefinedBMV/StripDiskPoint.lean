import RefinedBMV.StripDiskMap
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan

namespace RefinedBMV
open scoped ComplexOrder
set_option maxHeartbeats 400000

noncomputable def cubicDiskPoint : ℂ := ((1/Real.sqrt 3 : ℝ) : ℂ)

theorem cubicDiskPoint_norm_sq : ‖cubicDiskPoint‖^2 = (1/3 : ℝ) := by
  simp only [cubicDiskPoint,Complex.norm_real,Real.norm_eq_abs,abs_div,abs_one,
    abs_of_nonneg (Real.sqrt_nonneg 3),div_pow]
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

theorem cubicDiskPoint_mem : ‖cubicDiskPoint‖ < 1 := by
  have h := cubicDiskPoint_norm_sq
  nlinarith [norm_nonneg cubicDiskPoint]

theorem stripDiskCenter_eq_arctan (w : ℂ) :
    stripDiskCenter w = Complex.arctan w/(Real.pi : ℂ) := by
  simp only [stripDiskCenter,Complex.arctan,diskCayley,mul_comm Complex.I w,
    Complex.ofReal_mul,Complex.ofReal_ofNat,div_eq_mul_inv,mul_inv_rev]
  ring

theorem stripDiskInverse_cubic_point : stripDiskInverse cubicDiskPoint = (2/3 : ℂ) := by
  have hp : Real.pi ≠ 0 := Real.pi_pos.ne'
  have hpc : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast hp
  have ha : Real.arctan (1/Real.sqrt 3) = Real.pi/6 := by
    simpa only [one_div] using Real.arctan_inv_sqrt_three
  rw [stripDiskInverse,stripDiskCenter_eq_arctan,cubicDiskPoint,← Complex.ofReal_arctan,ha]
  simp only [Complex.ofReal_div,Complex.ofReal_ofNat]
  field_simp
  ring

/-- The principal-log formula is an actual right inverse of the strip-to-disk tangent map. -/
theorem stripDiskInverse_tan_right_inverse (w : ℂ) (hw : ‖w‖ < 1) :
    Complex.tan ((Real.pi : ℂ)*(stripDiskInverse w-1/2)) = w := by
  have hpc : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  have he : (Real.pi : ℂ)*(stripDiskInverse w-1/2) = Complex.arctan w := by
    rw [stripDiskInverse,stripDiskCenter_eq_arctan]
    field_simp
    ring
  have hI : w ≠ Complex.I := by
    intro heq
    rw [heq,Complex.norm_I] at hw
    exact (lt_irrefl 1) hw
  have hnegI : w ≠ -Complex.I := by
    intro heq
    rw [heq,norm_neg,Complex.norm_I] at hw
    exact (lt_irrefl 1) hw
  rw [he]
  exact Complex.tan_arctan hI hnegI

end RefinedBMV
