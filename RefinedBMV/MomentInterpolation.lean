import RefinedBMV.QuarticInterpolation

namespace RefinedBMV
open Filter Topology Metric Set
set_option maxHeartbeats 500000

theorem moment_interpolation_scalar (f : ℂ → ℂ) (S C θ : ℝ) (p : ℕ)
    (hS : 0 < S) (hC : 0 ≤ C) (hp : 0 < p) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hf : Differentiable ℂ f)
    (hbounded : ∃ K : ℝ, ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → ‖f z‖ ≤ K)
    (hleft : ∀ z : ℂ, z.re = 0 → ‖f z‖ ≤ S)
    (hright : ∀ z : ℂ, z.re = 1 → ‖f z‖^p ≤ C*S^(p-1))
    (hpoint : ‖f (θ : ℂ)‖ = S) : S ≤ C := by
  let g : ℂ → ℂ := fun z => f z/(S : ℂ)
  let R : ℝ := (C/S)^(1/(p : ℝ))
  have hr0 : 0 ≤ C/S := div_nonneg hC hS.le
  have hR0 : 0 ≤ R := Real.rpow_nonneg hr0 _
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hRp : R^p = C/S := by
    dsimp [R]
    rw [← Real.rpow_natCast,← Real.rpow_mul hr0]
    rw [one_div_mul_cancel hp'.ne',Real.rpow_one]
  have hg : Differentiable ℂ g := hf.div_const _
  have hnorm (z : ℂ) : ‖g z‖ = ‖f z‖/S := by
    simp only [g,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hS]
  have hL : ∀ z : ℂ, z.re = 0 → ‖g z‖ ≤ 1 := by
    intro z hz
    rw [hnorm,div_le_one₀ hS]
    exact hleft z hz
  have hR : ∀ z : ℂ, z.re = 1 → ‖g z‖ ≤ R := by
    intro z hz
    apply (pow_le_pow_iff_left₀ (norm_nonneg _) hR0 hp.ne').mp
    rw [hRp,hnorm,div_pow]
    apply (div_le_div_iff₀ (pow_pos hS p) hS).mpr
    have he := mul_le_mul_of_nonneg_right (hright z hz) hS.le
    have hpow : S^(p-1)*S = S^p := by
      rw [← pow_succ,Nat.sub_add_cancel hp]
    simpa only [mul_assoc,hpow] using he
  obtain ⟨K,hK⟩ := hbounded
  have hb : BddAbove ((norm ∘ g) '' Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
    refine ⟨K/S,?_⟩
    rintro _ ⟨z,hz,rfl⟩
    rw [Function.comp_apply,hnorm]
    exact div_le_div_of_nonneg_right (hK z hz.1 hz.2) hS.le
  have hP : ‖g (θ : ℂ)‖ = 1 := by rw [hnorm,hpoint,div_self hS.ne']
  have h := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁'
    (f := g) (z := (θ : ℂ)) (a := (1 : ℝ)) (b := R)
    (by exact ⟨hθ.le,hθ1⟩) hg.diffContOnCl hb hL hR
  rw [hP] at h
  simp only [Complex.ofReal_re,Real.one_rpow,one_mul] at h
  have he : R^θ = (C/S)^((1/(p : ℝ))*θ) := by
    exact (Real.rpow_mul hr0 _ _).symm
  rw [he] at h
  have h1 : (1 : ℝ)^((1/(p : ℝ))*θ) ≤ (C/S)^((1/(p : ℝ))*θ) := by simpa using h
  have hh := (Real.rpow_le_rpow_iff zero_le_one hr0 (mul_pos (one_div_pos.mpr hp') hθ)).mp h1
  simpa only [one_mul] using (le_div_iff₀ hS).mp hh

/-- Dual trace interpolation between the weighted unitary and Hilbert--Schmidt endpoints. -/
theorem dual_moment_interpolation (f : ℂ → ℂ) (S T : ℝ) (q : ℕ)
    (hS : 0 < S) (hT : 0 ≤ T) (hq : 0 < q)
    (hf : Differentiable ℂ f)
    (hbounded : ∃ K : ℝ, ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → ‖f z‖ ≤ K)
    (hleft : ∀ z : ℂ, z.re = 0 → ‖f z‖ ≤ S)
    (hright : ∀ z : ℂ, z.re = 1 → ‖f z‖^2 ≤ T*S) :
    ‖f ((1/(q : ℝ) : ℝ) : ℂ)‖^(2*q) ≤ T*S^(2*q-1) := by
  let g : ℂ → ℂ := fun z => f z/(S : ℂ)
  let R : ℝ := (T/S)^(1/2 : ℝ)
  have hr : 0 ≤ T/S := div_nonneg hT hS.le
  have hR0 : 0 ≤ R := Real.rpow_nonneg hr _
  have hR2 : R^2 = T/S := by
    dsimp [R]
    rw [← Real.rpow_natCast,← Real.rpow_mul hr]
    norm_num
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hg : Differentiable ℂ g := hf.div_const _
  have hnorm (z : ℂ) : ‖g z‖ = ‖f z‖/S := by
    simp only [g,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hS]
  have hL : ∀ z : ℂ, z.re = 0 → ‖g z‖ ≤ 1 := by
    intro z hz
    rw [hnorm,div_le_one₀ hS]
    exact hleft z hz
  have hR : ∀ z : ℂ, z.re = 1 → ‖g z‖ ≤ R := by
    intro z hz
    apply (sq_le_sq₀ (norm_nonneg _) hR0).mp
    rw [hR2,hnorm,div_pow]
    apply (div_le_div_iff₀ (pow_pos hS 2) hS).mpr
    have he := mul_le_mul_of_nonneg_right (hright z hz) hS.le
    convert he using 1
    ring
  obtain ⟨K,hK⟩ := hbounded
  have hb : BddAbove ((norm ∘ g) '' Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
    refine ⟨K/S,?_⟩
    rintro _ ⟨z,hz,rfl⟩
    rw [Function.comp_apply,hnorm]
    exact div_le_div_of_nonneg_right (hK z hz.1 hz.2) hS.le
  have h := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁'
    (f := g) (z := ((1/(q : ℝ) : ℝ) : ℂ)) (a := (1 : ℝ)) (b := R)
    (by exact ⟨(one_div_pos.mpr hqR).le,(div_le_one₀ hqR).mpr hq1⟩) hg.diffContOnCl hb hL hR
  simp only [Complex.ofReal_re,Real.one_rpow,one_mul] at h
  have he : R^(1/(q : ℝ)) = (T/S)^(1/(2*(q : ℝ))) := by
    dsimp [R]
    rw [← Real.rpow_mul hr]
    congr 1
    ring
  rw [he] at h
  have hp0 : 0 < 2*q := by omega
  have hh := pow_le_pow_left₀ (norm_nonneg _) h (2*q)
  have heq : ((T/S)^(1/(2*(q : ℝ))))^(2*q) = T/S := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hr]
    push_cast
    rw [one_div_mul_cancel (mul_pos (by norm_num) hqR).ne',Real.rpow_one]
  rw [heq,hnorm,div_pow] at hh
  have hc := (div_le_div_iff₀ (pow_pos hS (2*q)) hS).mp hh
  have hpow : S^(2*q-1)*S = S^(2*q) := by rw [← pow_succ,Nat.sub_add_cancel hp0]
  apply (mul_le_mul_iff_of_pos_right hS).mp
  simpa only [mul_assoc,hpow] using hc

end RefinedBMV
