import RefinedBMV.WordAverage
import Mathlib.Tactic.Positivity

namespace RefinedBMV

/-- The second exact expression for the complete average in (7.15). -/
theorem cubic_average_deficit {d} (A B : Mat d) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    p 3 3 A B - reTrace ((A*B)^3) = (3/10 : ℝ) *
      (reTrace (A^3*B^3) + 2*reTrace (A^2*B*A*B^2) - 3*reTrace ((A*B)^3)) := by
  rw [identity33 A B hA hB]
  simp [trWord, evalWord, pow_succ, mul_assoc]
  ring

/-- The scalar identity (7.13), with its actual nonzero denominator. -/
theorem cubic_margin_identity (x : ℝ) (hx : x ≤ 1) :
    1 + 2*x*(3*x-1)/(3-x) - 3*x^2 = 3*(1-x)^2*(1+x)/(3-x) := by
  have hn : 3-x ≠ 0 := by linarith
  field_simp
  ring

theorem cubic_margin_nonneg (D x : ℝ) (hD : 0 ≤ D) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ 3*D*(1-x)^2*(1+x)/(3-x) := by
  have hn : 0 < 3-x := by linarith
  positivity

/-- The complete scalar return from estimate (7.12) to the joint estimate (7.13). -/
theorem cubic_joint_of_ratio_bound (D C W x : ℝ) (hD : 0 ≤ D)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hC : C = D*x^2)
    (hW : D*x*(3*x-1)/(3-x) ≤ W) :
    3*D*(1-x)^2*(1+x)/(3-x) ≤ D+2*W-3*C ∧ 3*C ≤ D+2*W := by
  have hn : 3-x ≠ 0 := by linarith
  have he : D + 2*(D*x*(3*x-1)/(3-x)) - 3*C =
      3*D*(1-x)^2*(1+x)/(3-x) := by
    rw [hC]
    field_simp
    ring
  have hmargin := cubic_margin_nonneg D x hD hx0 hx1
  constructor <;> linarith

/-- The real-coordinate disk calculation in (7.10); it includes a=1. -/
theorem mobius_disk_left_bound (a u v : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hdisc : 9*((u-a)^2+v^2) ≤ (1-a*u)^2 + (a*v)^2) :
    (3*a-1)/(3-a) ≤ u := by
  have hden : 0 < 3-a := by linarith
  have ha2 : a^2 ≤ 1 := by nlinarith
  have hv : 0 ≤ (9-a^2)*v^2 := mul_nonneg (by nlinarith) (sq_nonneg v)
  have hscalar : 9*(u-a)^2 ≤ (1-a*u)^2 := by nlinarith
  apply (div_le_iff₀ hden).mpr
  by_contra hbad
  have hl : (3-a)*u-(3*a-1) < 0 := by linarith
  have hr : (3+a)*u-(3*a+1) < 0 := by
    have hc : (3-a)*((3+a)*u-(3*a+1)) =
        (3+a)*((3-a)*u-(3*a-1)) - 6*(1-a^2) := by ring
    have hneg : (3+a)*((3-a)*u-(3*a-1)) < 0 := mul_neg_of_pos_of_neg (by linarith) hl
    nlinarith
  have hp : 0 < ((3-a)*u-(3*a-1))*((3+a)*u-(3*a+1)) := mul_pos_of_neg_of_neg hl hr
  have he : ((3-a)*u-(3*a-1))*((3+a)*u-(3*a+1)) =
      9*(u-a)^2-(1-a*u)^2 := by ring
  rw [he] at hp
  linarith

end RefinedBMV
