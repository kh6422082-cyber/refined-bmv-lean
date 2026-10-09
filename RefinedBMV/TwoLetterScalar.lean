import RefinedBMV.OneLetter
import Mathlib.Data.Fin.Rev

namespace RefinedBMV

theorem two_sqrt_product_le_add (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    2*Real.sqrt (u*v) ≤ u+v := by
  rw [Real.sqrt_mul hu]
  have hs := sq_nonneg (Real.sqrt u - Real.sqrt v)
  nlinarith [Real.sq_sqrt hu, Real.sq_sqrt hv]

theorem monomial_pair_lower (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (n r : ℕ) (hr : r ≤ n) :
    2*Real.sqrt ((a*b)^n) ≤ a^r*b^(n-r) + a^(n-r)*b^r := by
  have hu : 0 ≤ a^r*b^(n-r) := mul_nonneg (pow_nonneg ha _) (pow_nonneg hb _)
  have hv : 0 ≤ a^(n-r)*b^r := mul_nonneg (pow_nonneg ha _) (pow_nonneg hb _)
  have he : (a^r*b^(n-r))*(a^(n-r)*b^r) = (a*b)^n := by
    have h1 : r+(n-r) = n := by omega
    have h2 : (n-r)+r = n := by omega
    calc
      (a^r*b^(n-r))*(a^(n-r)*b^r) = (a^r*a^(n-r))*(b^(n-r)*b^r) := by ring
      _ = (a*b)^n := by rw [← pow_add, ← pow_add, h1, h2, mul_pow]
  simpa only [he] using two_sqrt_product_le_add _ _ hu hv

theorem sqrt_nat_power (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    Real.sqrt (x^n) = x^((n : ℝ)/2) := by
  calc
    Real.sqrt (x^n) = (x^n)^(1/2 : ℝ) := Real.sqrt_eq_rpow _
    _ = (x^(n : ℝ))^(1/2 : ℝ) := by rw [Real.rpow_natCast]
    _ = x^((n : ℝ)/2) := by rw [← Real.rpow_mul hx]; congr 1; ring

/-- The scalar AM--GM inequality used in (3.6), including zero eigenvalues. -/
theorem two_letter_scalar_average (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) :
    (a*b)^((n : ℝ)/2) ≤
      (∑ r : Fin (n+1), a^(r : ℕ)*b^(n-r)) / (n+1) := by
  let f : Fin (n+1) → ℝ := fun r => a^(r : ℕ)*b^(n-r)
  have hp (r : Fin (n+1)) : 2*Real.sqrt ((a*b)^n) ≤ f r + f r.rev := by
    have hr : (r : ℕ) ≤ n := by omega
    have he1 : (r.rev : ℕ) = n-r := by simp only [Fin.val_rev]; omega
    have he2 : n-(r.rev : ℕ) = r := by rw [he1]; omega
    change 2*Real.sqrt ((a*b)^n) ≤ a^(r : ℕ)*b^(n-r) + a^(r.rev : ℕ)*b^(n-r.rev)
    rw [he2, he1]
    exact monomial_pair_lower a b ha hb n r hr
  have hs := Finset.sum_le_sum (fun r (_ : r ∈ Finset.univ) => hp r)
  have he : (∑ r : Fin (n+1), f r.rev) = ∑ r : Fin (n+1), f r :=
    by simpa using (Fin.revPerm : Equiv.Perm (Fin (n+1))).sum_comp Finset.univ f
  rw [Finset.sum_add_distrib, he] at hs
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  simp only [Nat.cast_add, Nat.cast_one] at hs
  have hpos : (0 : ℝ) < n+1 := by positivity
  rw [← sqrt_nat_power (a*b) (mul_nonneg ha hb) n]
  apply (le_div_iff₀ hpos).mpr
  change Real.sqrt ((a*b)^n) * (n+1) ≤ ∑ r, f r
  linarith

end RefinedBMV
