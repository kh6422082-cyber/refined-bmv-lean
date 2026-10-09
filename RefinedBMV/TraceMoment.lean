import RefinedBMV.Reversed45

namespace RefinedBMV
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 600000

def traceMoment {d} (q : ℕ) (M : Mat d) : ℝ := reTrace ((star M*M)^q)

theorem traceMoment_nonneg {d} (q : ℕ) (M : Mat d) : 0 ≤ traceMoment q M :=
  (RCLike.nonneg_iff.mp ((Matrix.posSemidef_conjTranspose_mul_self M).pow q).trace_nonneg).1

theorem complexPower_pow {d} (A : Mat d) (z : ℂ) (k : ℕ) :
    (complexPower A z)^k = complexPower A ((k : ℂ)*z) := by
  induction k with
  | zero => simp [complexPower]
  | succ k hk =>
    rw [pow_succ,hk,← complexPower_add]
    congr 1
    push_cast
    ring

theorem traceMoment_complexPower {d} (P : Mat d) (q : ℕ) (r : ℝ) :
    traceMoment q (complexPower P (r : ℂ)) =
      reTrace (complexPower P ((2*(q : ℝ)*r : ℝ) : ℂ)) := by
  rw [traceMoment,complexPower_star]
  simp only [show star (r : ℂ) = (r : ℂ) by simp,← complexPower_add,complexPower_pow]
  congr 2
  push_cast
  ring

theorem traceMoment_root {d} (P : Mat d) (hP : P.PosDef) (N q : ℕ) (hq : q ≠ 0) :
    traceMoment q (complexPower P (((N : ℝ)/(2*q) : ℝ) : ℂ)) = reTrace (P^N) := by
  rw [traceMoment_complexPower]
  have he : 2*(q : ℝ)*((N : ℝ)/(2*q)) = (N : ℝ) := by
    have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq
    field_simp
  rw [he]
  simpa using congrArg reTrace (complexPower_nat P hP N)

theorem hsSquared_root {d} (P : Mat d) (hP : P.PosDef) (N : ℕ) :
    hsSquared (complexPower P (((N : ℝ)/2 : ℝ) : ℂ)) = reTrace (P^N) := by
  have h := traceMoment_root P hP N 1 (by norm_num)
  norm_num [traceMoment] at h
  norm_num [hsSquared]
  exact h

theorem hsFourth_root {d} (P : Mat d) (hP : P.PosDef) (N : ℕ) :
    hsFourth (complexPower P (((N : ℝ)/4 : ℝ) : ℂ)) = reTrace (P^N) := by
  have h := traceMoment_root P hP N 2 (by norm_num)
  norm_num [traceMoment] at h
  norm_num [hsFourth]
  exact h

theorem hsEighth_root {d} (P : Mat d) (hP : P.PosDef) (N : ℕ) :
    hsEighth (complexPower P (((N : ℝ)/8 : ℝ) : ℂ)) = reTrace (P^N) := by
  have h := traceMoment_root P hP N 4 (by norm_num)
  norm_num [traceMoment] at h
  norm_num [hsEighth]
  exact h

theorem traceMoment_star {d} (q : ℕ) (M : Mat d) : traceMoment q (star M) = traceMoment q M := by
  simp only [traceMoment,star_star]
  exact reTrace_mul_pow _ _ q

theorem traceMoment_right_unitary {d} (q : ℕ) (M U : Mat d) (hU : U ∈ unitary (Mat d)) :
    traceMoment q (M*U) = traceMoment q M := by
  have he : star (M*U)*(M*U) = star U*(star M*M)*U := by
    simp only [star_mul,mul_assoc]
  rw [traceMoment,he]
  exact reTrace_unitary_reverse_conj_pow U (star M*M) hU q

theorem traceMoment_left_unitary {d} (q : ℕ) (U M : Mat d) (hU : U ∈ unitary (Mat d)) :
    traceMoment q (U*M) = traceMoment q M := by
  rw [← traceMoment_star q (U*M),star_mul,
    traceMoment_right_unitary _ _ _ (Unitary.star_mem hU),traceMoment_star]

theorem traceMoment_polar {d} (q : ℕ) (M P : Mat d) (hPP : P*P = star M*M) :
    traceMoment q M = reTrace (P^(2*q)) := by
  rw [traceMoment,← hPP,← pow_two,← pow_mul]

end RefinedBMV
