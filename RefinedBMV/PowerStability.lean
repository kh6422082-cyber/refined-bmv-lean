import RefinedBMV.ALTFamilies
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Basic

namespace RefinedBMV
open Filter Topology
set_option maxHeartbeats 600000

section NormedRing
variable {R : Type*} [NormedRing R] [NormOneClass R]

/-- A power difference bound that does not assume the two factors commute. -/
theorem norm_pow_sub_le_ge_one (a b : R) (C : ℝ) (hC : 1 ≤ C)
    (ha : ‖a‖ ≤ C) (hb : ‖b‖ ≤ C) (n : ℕ) :
    ‖a^n-b^n‖ ≤ (n : ℝ)*C^n*‖a-b‖ := by
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  induction n with
  | zero => simp
  | succ n hn =>
    have he : a^(n+1)-b^(n+1) = a*(a^n-b^n)+(a-b)*b^n := by
      simp only [pow_succ']
      noncomm_ring
    have hbn : ‖b^n‖ ≤ C^n := (norm_pow_le b n).trans (pow_le_pow_left₀ (norm_nonneg _) hb n)
    calc
      ‖a^(n+1)-b^(n+1)‖ = ‖a*(a^n-b^n)+(a-b)*b^n‖ := by rw [he]
      _ ≤ ‖a*(a^n-b^n)‖+‖(a-b)*b^n‖ := norm_add_le _ _
      _ ≤ ‖a‖*‖a^n-b^n‖+‖a-b‖*‖b^n‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ C*((n : ℝ)*C^n*‖a-b‖)+‖a-b‖*C^n := by gcongr
      _ = ((n : ℝ)*C+1)*(C^n*‖a-b‖) := by ring
      _ ≤ (((n : ℝ)+1)*C)*(C^n*‖a-b‖) :=
        mul_le_mul_of_nonneg_right (by nlinarith) (mul_nonneg (pow_nonneg hC0 _) (norm_nonneg _))
      _ = ((n+1 : ℕ) : ℝ)*C^(n+1)*‖a-b‖ := by rw [pow_succ]; push_cast; ring

end NormedRing

theorem one_add_div_pow_le_exp (C : ℝ) (hC : 0 ≤ C) (n : ℕ) :
    (1+C/(n : ℝ))^n ≤ Real.exp C := by
  have h := Real.one_sub_div_pow_le_exp_neg (n := n) (t := -C)
    (by have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
  simpa only [neg_div,sub_neg_eq_add,neg_neg] using h

section FirstOrder
variable {R : Type*} [NormedRing R] [NormOneClass R] [NormedAlgebra ℝ R]

theorem first_order_norm_bound (f : ℝ → R) (H : R) (hf0 : f 0=1)
    (hf : HasDerivAt f H 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ t : ℝ in 𝓝 0, ‖f t‖ ≤ 1+C*|t| := by
  obtain ⟨C,hC,hb⟩ := hf.isBigO_sub.exists_nonneg
  refine ⟨C,hC,?_⟩
  filter_upwards [hb.bound] with t ht
  simp only [hf0,sub_zero,Real.norm_eq_abs] at ht
  calc
    ‖f t‖ = ‖(f t-1)+1‖ := by rw [sub_add_cancel]
    _ ≤ ‖f t-1‖+‖(1 : R)‖ := norm_add_le _ _
    _ ≤ 1+C*|t| := by rw [norm_one]; linarith

/-- Identical first-order behavior at the identity makes reciprocal-step powers
asymptotically identical, with no commutativity assumption. -/
theorem reciprocal_power_stability (f g : ℝ → R) (H : R)
    (hf0 : f 0=1) (hg0 : g 0=1) (hf : HasDerivAt f H 0) (hg : HasDerivAt g H 0) :
    Tendsto (fun k : ℕ => (f (1/(k : ℝ)))^k-(g (1/(k : ℝ)))^k) atTop (𝓝 0) := by
  have ht : Tendsto (fun k : ℕ => 1/(k : ℝ)) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
  have hd : HasDerivAt (fun t => f t-g t) 0 (0 : ℝ) := by
    convert! hf.sub hg using 1
    simp only [sub_self]
  have hsmall := (hasDerivAt_iff_tendsto.mp hd).comp ht
  have herr : Tendsto (fun k : ℕ => (k : ℝ)*‖f (1/(k : ℝ))-g (1/(k : ℝ))‖) atTop (𝓝 0) := by
    simpa only [Function.comp_def,hf0,hg0,sub_self,sub_zero,smul_zero,one_div,norm_inv,Real.norm_natCast,inv_inv] using hsmall
  obtain ⟨Cf,hCf,hfb⟩ := first_order_norm_bound f H hf0 hf
  obtain ⟨Cg,hCg,hgb⟩ := first_order_norm_bound g H hg0 hg
  let C := Cf+Cg
  have hC : 0 ≤ C := add_nonneg hCf hCg
  have hbound : ∀ᶠ k : ℕ in atTop,
      ‖(f (1/(k : ℝ)))^k-(g (1/(k : ℝ)))^k‖ ≤
        Real.exp C*((k : ℝ)*‖f (1/(k : ℝ))-g (1/(k : ℝ))‖) := by
    filter_upwards [ht.eventually hfb,ht.eventually hgb] with k hfk hgk
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have habs : |1/(k : ℝ)| = 1/(k : ℝ) := abs_of_nonneg (by positivity)
    rw [habs] at hfk hgk
    have hfn : ‖f (1/(k : ℝ))‖ ≤ 1+C/(k : ℝ) := by
      have hcf : Cf ≤ C := by dsimp [C]; linarith
      calc
        _ ≤ 1+Cf*(1/(k : ℝ)) := hfk
        _ ≤ 1+C/(k : ℝ) := by simp only [mul_one_div]; gcongr
    have hgn : ‖g (1/(k : ℝ))‖ ≤ 1+C/(k : ℝ) := by
      have hcg : Cg ≤ C := by dsimp [C]; linarith
      calc
        _ ≤ 1+Cg*(1/(k : ℝ)) := hgk
        _ ≤ 1+C/(k : ℝ) := by simp only [mul_one_div]; gcongr
    have hbase : 1 ≤ 1+C/(k : ℝ) := le_add_of_nonneg_right (div_nonneg hC hk0)
    have h := norm_pow_sub_le_ge_one (f (1/(k : ℝ))) (g (1/(k : ℝ))) _ hbase hfn hgn k
    calc
      _ ≤ (k : ℝ)*(1+C/(k : ℝ))^k*‖f (1/(k : ℝ))-g (1/(k : ℝ))‖ := h
      _ ≤ (k : ℝ)*Real.exp C*‖f (1/(k : ℝ))-g (1/(k : ℝ))‖ := by
        gcongr
        exact one_add_div_pow_le_exp C hC k
      _ = _ := by ring
  have hzero : Tendsto (fun k : ℕ => Real.exp C*((k : ℝ)*‖f (1/(k : ℝ))-g (1/(k : ℝ))‖)) atTop (𝓝 0) := by
    simpa using herr.const_mul (Real.exp C)
  exact squeeze_zero_norm' hbound hzero

end FirstOrder
end RefinedBMV
