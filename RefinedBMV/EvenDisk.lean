import RefinedBMV.CubicScalar
import Mathlib.Analysis.Complex.Schwarz

namespace RefinedBMV
open Filter Topology Metric Set
set_option maxHeartbeats 500000

theorem even_disk_hasDerivAt_zero (h : ℂ → ℂ)
    (hd : DifferentiableOn ℂ h (ball 0 1))
    (heven : ∀ w ∈ ball (0 : ℂ) 1, h (-w) = h w) : HasDerivAt h 0 0 := by
  have hd0 : DifferentiableAt ℂ h 0 := hd.differentiableAt (ball_mem_nhds _ (by norm_num))
  have hp := hd0.hasDerivAt
  have hn : HasDerivAt (fun w => h (-w)) (-deriv h 0) 0 := by
    have hpneg : HasDerivAt h (deriv h 0) (-(0 : ℂ)) := by rw [neg_zero]; exact hp
    have hc := HasDerivAt.scomp (𝕜 := ℂ) (𝕜' := ℂ) (F := ℂ)
      (g₁ := h) (g₁' := deriv h 0) (h := fun z : ℂ => -z) (0 : ℂ)
      hpneg (hasDerivAt_neg (0 : ℂ))
    convert! hc using 1
    simp
  have he : h =ᶠ[𝓝 (0 : ℂ)] (fun w => h (-w)) :=
    Filter.eventually_of_mem (ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1))
      (fun w hw => (heven w hw).symm)
  have hn' := hn.congr_of_eventuallyEq he
  have hz : deriv h 0 = 0 := by
    have hx := hn'.unique hp
    have h2 : (2 : ℂ)*deriv h 0 = 0 := by linear_combination -hx
    exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
  simpa only [hz] using hp

theorem mobius_norm_bound (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (u : ℂ) (hu : ‖u‖ ≤ 1) :
    1-(a : ℂ)*u ≠ 0 ∧ ‖(u-(a : ℂ))/(1-(a : ℂ)*u)‖ ≤ 1 := by
  have ha : ‖(a : ℂ)‖ = a := by simp [abs_of_nonneg ha0]
  have hlt : ‖(a : ℂ)*u‖ < 1 := by
    rw [norm_mul,ha]
    exact (mul_le_mul_of_nonneg_left hu ha0).trans_lt (by simpa using ha1)
  have hne : 1-(a : ℂ)*u ≠ 0 := by
    intro he
    have hz : (a : ℂ)*u = 1 := by linear_combination -he
    rw [hz,norm_one] at hlt
    exact (lt_irrefl 1) hlt
  refine ⟨hne, ?_⟩
  have hnorm : ‖u‖^2 ≤ 1 := by nlinarith [norm_nonneg u]
  have hapos : 0 ≤ 1-a^2 := by nlinarith
  have hprod := mul_nonneg hapos (show 0 ≤ 1-‖u‖^2 by linarith)
  have hs : ‖u-(a : ℂ)‖^2 ≤ ‖1-(a : ℂ)*u‖^2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re,Complex.sub_im,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.one_re,Complex.one_im,zero_mul,add_zero,sub_zero] at hprod ⊢
    nlinarith only [hprod]
  rw [norm_div,div_le_one₀ (norm_pos_iff.mpr hne)]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs

/-- A second-order Schwarz estimate avoids choosing a square-root branch for an even function. -/
theorem even_disk_mobius_bound (h : ℂ → ℂ) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hd : DifferentiableOn ℂ h (ball 0 1))
    (heven : ∀ w ∈ ball (0 : ℂ) 1, h (-w) = h w)
    (hb : ∀ w ∈ ball (0 : ℂ) 1, ‖h w‖ ≤ 1) (h0 : h 0 = (a : ℂ))
    (w : ℂ) (hw : w ∈ ball (0 : ℂ) 1) :
    ‖h w-(a : ℂ)‖ ≤ ‖w‖^2*‖1-(a : ℂ)*h w‖ := by
  let g : ℂ → ℂ := fun z => (h z-(a : ℂ))/(1-(a : ℂ)*h z)
  have hden : ∀ z ∈ ball (0 : ℂ) 1, 1-(a : ℂ)*h z ≠ 0 :=
    fun z hz => (mobius_norm_bound a ha0 ha1 (h z) (hb z hz)).1
  have hgd : DifferentiableOn ℂ g (ball 0 1) :=
    (hd.sub_const _).div ((differentiableOn_const _).sub ((differentiableOn_const _).mul hd)) hden
  have hg0 : g 0 = 0 := by simp [g,h0]
  have hge : ∀ z ∈ ball (0 : ℂ) 1, g (-z) = g z := by
    intro z hz
    simp only [g,heven z hz]
  have hgderiv := even_disk_hasDerivAt_zero g hgd hge
  have ho : (fun z => g z-g 0) =o[𝓝 (0 : ℂ)] (fun z => ‖z-0‖^1) := by
    simpa only [smul_zero,sub_zero,pow_one] using hgderiv.isLittleO.norm_right
  have hm : MapsTo g (ball 0 1) (closedBall (g 0) 1) := by
    intro z hz
    rw [mem_closedBall,dist_eq_norm,hg0,sub_zero]
    exact (mobius_norm_bound a ha0 ha1 (h z) (hb z hz)).2
  have hs := Complex.dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO
    (n := 1) hgd hm ho hw
  simp only [dist_eq_norm,hg0,sub_zero,div_one,one_mul] at hs
  change ‖(h w-(a : ℂ))/(1-(a : ℂ)*h w)‖ ≤ ‖w‖^2 at hs
  rw [norm_div] at hs
  exact (div_le_iff₀ (norm_pos_iff.mpr (hden w hw))).mp hs

/-- The disk lower estimate (7.9), including the constant boundary case a=1. -/
theorem even_disk_point_lower (h : ℂ → ℂ) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hd : DifferentiableOn ℂ h (ball 0 1))
    (heven : ∀ w ∈ ball (0 : ℂ) 1, h (-w) = h w)
    (hb : ∀ w ∈ ball (0 : ℂ) 1, ‖h w‖ ≤ 1) (h0 : h 0 = (a : ℂ))
    (w : ℂ) (hw2 : ‖w‖^2 = (1/3 : ℝ)) :
    (3*a-1)/(3-a) ≤ (h w).re := by
  have hw : w ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball,dist_eq_norm,sub_zero]
    nlinarith [norm_nonneg w]
  have hz0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := by simp
  rcases lt_or_eq_of_le ha1 with ha | rfl
  · have hs := even_disk_mobius_bound h a ha0 ha hd heven hb h0 w hw
    rw [hw2] at hs
    have hs2 := pow_le_pow_left₀ (norm_nonneg _) hs 2
    have hdisc : 9*(((h w).re-a)^2+(h w).im^2) ≤
        (1-a*(h w).re)^2+(a*(h w).im)^2 := by
      simp only [mul_pow,Complex.sq_norm,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,
        Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
        Complex.one_re,Complex.one_im,zero_mul,add_zero,sub_zero] at hs2
      nlinarith only [hs2]
    exact mobius_disk_left_bound a (h w).re (h w).im ha0 ha1 hdisc
  · have hm : IsMaxOn (norm ∘ h) (ball (0 : ℂ) 1) 0 := by
      rw [isMaxOn_iff]
      intro z hz
      simpa only [Function.comp_apply,h0,Complex.ofReal_one,norm_one] using hb z hz
    have he := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm
      (convex_ball (0 : ℂ) 1).isPreconnected isOpen_ball hd hz0 hm hw
    simp only [Function.const] at he
    rw [he,h0]
    norm_num

end RefinedBMV
