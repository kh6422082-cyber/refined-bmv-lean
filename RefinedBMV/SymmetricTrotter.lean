import RefinedBMV.PowerStability

namespace RefinedBMV
open Filter Topology
open scoped Matrix.Norms.L2Operator
set_option maxHeartbeats 600000

/-- The symmetric one-step product, defined for arbitrary complex matrices. -/
noncomputable def trotterStep {d} (F G : Mat d) (t : ℝ) : Mat d :=
  NormedSpace.exp (t • ((1/2 : ℝ) • F))*NormedSpace.exp (t • G)*
    NormedSpace.exp (t • ((1/2 : ℝ) • F))

theorem trotterStep_zero {d} (F G : Mat d) : trotterStep F G 0=1 := by
  simp [trotterStep]

theorem trotterStep_hasDerivAt_zero {d} (F G : Mat d) :
    HasDerivAt (trotterStep F G) (F+G) (0 : ℝ) := by
  have hF : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • ((1/2 : ℝ) • F)))
      ((1/2 : ℝ) • F) 0 := by
    simpa only [zero_smul,NormedSpace.exp_zero,one_mul] using
      hasDerivAt_exp_smul_const ((1/2 : ℝ) • F) (0 : ℝ)
  have hG : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • G)) G 0 := by
    simpa only [zero_smul,NormedSpace.exp_zero,one_mul] using
      hasDerivAt_exp_smul_const G (0 : ℝ)
  have h := (hF.mul hG).mul hF
  simp only [Pi.mul_apply,zero_smul,NormedSpace.exp_zero,one_mul,mul_one] at h
  have he : (1/2 : ℝ) • F+G+(1/2 : ℝ) • F = F+G := by
    calc
      _ = ((1/2 : ℝ) • F+(1/2 : ℝ) • F)+G := by abel
      _ = F+G := by rw [← add_smul]; norm_num
  rw [he] at h
  exact h

theorem reciprocal_exp_pow {d} (H : Mat d) (k : ℕ) (hk : 0 < k) :
    (NormedSpace.exp ((1/(k : ℝ)) • H))^k = NormedSpace.exp H := by
  let : NormedAlgebra ℚ (Mat d) := NormedAlgebra.restrictScalars ℚ ℝ (Mat d)
  rw [← NormedSpace.exp_nsmul]
  congr 1
  rw [← Nat.cast_smul_eq_nsmul ℝ,smul_smul,
    mul_one_div_cancel (by exact_mod_cast hk.ne' : (k : ℝ) ≠ 0),one_smul]

/-- Finite-dimensional symmetric Lie--Trotter convergence in operator norm;
neither Hermitian inputs nor commutativity are needed for this limit. -/
theorem symmetric_trotter_tendsto {d} (hdim : 0 < d) (F G : Mat d) :
    Tendsto (fun k : ℕ => (trotterStep F G (1/(k : ℝ)))^k) atTop
      (𝓝 (NormedSpace.exp (F+G))) := by
  let : NeZero d := ⟨by omega⟩
  have hR : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • (F+G))) (F+G) 0 := by
    simpa only [zero_smul,NormedSpace.exp_zero,one_mul] using
      hasDerivAt_exp_smul_const (F+G) (0 : ℝ)
  have h := reciprocal_power_stability (trotterStep F G)
    (fun t : ℝ => NormedSpace.exp (t • (F+G))) (F+G) (trotterStep_zero F G)
    (by simp) (trotterStep_hasDerivAt_zero F G) hR
  have he : (fun k : ℕ => (trotterStep F G (1/(k : ℝ)))^k-
      (NormedSpace.exp ((1/(k : ℝ)) • (F+G)))^k) =ᶠ[atTop]
      (fun k : ℕ => (trotterStep F G (1/(k : ℝ)))^k-NormedSpace.exp (F+G)) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with k hk
    rw [reciprocal_exp_pow (F+G) k hk]
  exact tendsto_sub_nhds_zero_iff.mp (h.congr' he)

theorem symmetric_trotter_tendsto_multiple {d} (hdim : 0 < d) (F G : Mat d) (m : ℕ) :
    Tendsto (fun k : ℕ => (trotterStep F G (1/(k : ℝ)))^(m*k)) atTop
      (𝓝 (NormedSpace.exp (m • (F+G)))) := by
  let : NormedAlgebra ℚ (Mat d) := NormedAlgebra.restrictScalars ℚ ℝ (Mat d)
  have h := (symmetric_trotter_tendsto hdim F G).pow m
  simpa only [← pow_mul,Nat.mul_comm,← NormedSpace.exp_nsmul] using h

end RefinedBMV
