import RefinedBMV.CubicInterpolation

namespace RefinedBMV
open Filter Topology Metric Set
set_option maxHeartbeats 400000

theorem quartic_interpolation_scalar (f : ℂ → ℂ) (S C : ℝ) (hS : 0 < S) (hC : 0 ≤ C)
    (hf : Differentiable ℂ f)
    (hbounded : ∃ K : ℝ, ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → ‖f z‖ ≤ K)
    (hleft : ∀ z : ℂ, z.re = 0 → ‖f z‖ ≤ S)
    (hright : ∀ z : ℂ, z.re = 1 → ‖f z‖^8 ≤ C*S^7)
    (hpoint : ‖f (4/5)‖ = S) : S ≤ C := by
  let g : ℂ → ℂ := fun z => f z/(S : ℂ)
  let R : ℝ := (C/S)^(1/8 : ℝ)
  have hr0 : 0 ≤ C/S := div_nonneg hC hS.le
  have hR0 : 0 ≤ R := Real.rpow_nonneg hr0 _
  have hR8 : R^8 = C/S := by
    dsimp [R]
    rw [← Real.rpow_natCast,← Real.rpow_mul hr0]
    norm_num
  have hg : Differentiable ℂ g := hf.div_const _
  have hnorm (z : ℂ) : ‖g z‖ = ‖f z‖/S := by
    simp only [g,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hS]
  have hL : ∀ z : ℂ, z.re = 0 → ‖g z‖ ≤ 1 := by
    intro z hz
    rw [hnorm,div_le_one₀ hS]
    exact hleft z hz
  have hR : ∀ z : ℂ, z.re = 1 → ‖g z‖ ≤ R := by
    intro z hz
    apply (pow_le_pow_iff_left₀ (norm_nonneg _) hR0 (by norm_num : (8 : ℕ) ≠ 0)).mp
    rw [hR8,hnorm,div_pow]
    have hs8 : 0 < S^8 := pow_pos hS _
    apply (div_le_div_iff₀ hs8 hS).mpr
    have he := mul_le_mul_of_nonneg_right (hright z hz) hS.le
    convert he using 1
    ring
  obtain ⟨K,hK⟩ := hbounded
  have hb : BddAbove ((norm ∘ g) '' Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
    refine ⟨K/S,?_⟩
    rintro _ ⟨z,hz,rfl⟩
    rw [Function.comp_apply,hnorm]
    exact div_le_div_of_nonneg_right (hK z hz.1 hz.2) hS.le
  have hP : ‖g (4/5)‖ = 1 := by rw [hnorm,hpoint,div_self hS.ne']
  have h := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁'
    (f := g) (z := (4/5 : ℂ)) (a := (1 : ℝ)) (b := R)
    (by norm_num [Complex.HadamardThreeLines.verticalClosedStrip]) hg.diffContOnCl hb
    (fun z hz => hL z hz) (fun z hz => hR z hz)
  rw [hP] at h
  norm_num at h
  have he : R^(4/5 : ℝ) = (C/S)^(1/10 : ℝ) := by
    dsimp [R]
    rw [← Real.rpow_mul hr0]
    congr 1
    ring
  rw [he] at h
  have h1 : (1 : ℝ)^(1/10 : ℝ) ≤ (C/S)^(1/10 : ℝ) := by simpa using h
  have hh := (Real.rpow_le_rpow_iff zero_le_one hr0 (by norm_num : (0 : ℝ) < 1/10)).mp h1
  simpa only [one_mul] using (le_div_iff₀ hS).mp hh

end RefinedBMV
