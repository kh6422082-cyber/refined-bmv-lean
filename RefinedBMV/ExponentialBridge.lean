import RefinedBMV.SymmetricTrotter

namespace RefinedBMV
open Filter Topology
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator NNReal
set_option maxHeartbeats 600000

theorem complexPower_real_log {d} (A : Mat d) (r : ℝ) :
    CFC.log (complexPower A (r : ℂ)) = r • CFC.log A := by
  have hsm : (r : ℂ) • CFC.log A = r • CFC.log A := by
    ext i j
    simp only [Matrix.smul_apply,Complex.real_smul,smul_eq_mul]
  have hs : IsSelfAdjoint (r • CFC.log A) := (isSelfAdjoint_iff.mpr (star_trivial r)).smul .log
  rw [complexPower,hsm,CFC.log_exp _ hs]

theorem positivePower_eq_real_exp {d} (A : Mat d) (hA : A.PosDef) (r : ℝ≥0) (hr : 0 < r) :
    positivePower A r = NormedSpace.exp ((r : ℝ) • CFC.log A) := by
  rw [positivePower_eq_complexPower A hA r hr,complexPower]
  congr 1

noncomputable def cfcTrotterStep {d} (D B : Mat d) (k : ℕ) : Mat d :=
  positivePower D (1/(2*k))*positivePower B (1/(k : ℝ≥0))*positivePower D (1/(2*k))

theorem cfcTrotterStep_eq {d} (D B : Mat d) (hD : D.PosDef) (hB : B.PosDef)
    (k : ℕ) (hk : 0 < k) :
    cfcTrotterStep D B k = trotterStep (CFC.log D) (CFC.log B) (1/(k : ℝ)) := by
  rw [cfcTrotterStep,positivePower_eq_real_exp D hD _ (by positivity),
    positivePower_eq_real_exp B hB _ (by positivity),trotterStep,smul_smul]
  have hhalf : (((1 : ℝ≥0)/(2*k) : ℝ≥0) : ℝ) = (1/(k : ℝ))*(1/2) := by
    push_cast
    ring
  have hwhole : (((1 : ℝ≥0)/(k : ℝ≥0) : ℝ≥0) : ℝ) = 1/(k : ℝ) := by push_cast; rfl
  rw [hhalf,hwhole]

/-- The actual CFC fractional-power product in (3.2) has the required noncommuting limit. -/
theorem cfc_trotter_tendsto {d} (hdim : 0 < d) (D B : Mat d) (hD : D.PosDef) (hB : B.PosDef) (m : ℕ) :
    Tendsto (fun k : ℕ => (cfcTrotterStep D B k)^(m*k)) atTop
      (𝓝 (NormedSpace.exp (m • (CFC.log D+CFC.log B)))) := by
  have h := symmetric_trotter_tendsto_multiple hdim (CFC.log D) (CFC.log B) m
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with k hk
  rw [cfcTrotterStep_eq D B hD hB k hk]

theorem exponential_bridge_sandwich {d} (hdim : 0 < d) (D B : Mat d)
    (hD : D.PosDef) (hB : B.PosDef) (m : ℕ) (hm : 0 < m) :
    reTrace (NormedSpace.exp (m • (CFC.log D+CFC.log B))) ≤
      reTrace ((CFC.sqrt D*B*CFC.sqrt D)^m) := by
  have hL := reTrace_continuous.tendsto _ |>.comp (cfc_trotter_tendsto hdim D B hD hB m)
  apply le_of_tendsto_of_tendsto hL tendsto_const_nhds
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with k hk
  exact alt_trotter_approximants_le hdim D B k m hk hm hD.posSemidef hB.posSemidef

/-- Lemma 3.1 (CLBRIDGE), without a commutativity assumption or an assumed product limit. -/
theorem paper_lemma_3_1 {d} (hdim : 0 < d) (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (A B : Mat d) (hA : A.PosDef) (hB : B.PosDef) : paperL n m A B ≤ paperT n m A B := by
  let r : ℝ := (n : ℝ)/m
  let D := complexPower A (r : ℂ)
  have hD : D.PosDef := complexPower_real_posDef A hA r
  have h := exponential_bridge_sandwich hdim D B hD hB m hm
  have hlog : CFC.log D = r • CFC.log A := complexPower_real_log A r
  have hsm : m • (CFC.log D+CFC.log B) = n • CFC.log A+m • CFC.log B := by
    rw [smul_add,hlog,← Nat.cast_smul_eq_nsmul ℝ,smul_smul]
    have he : (m : ℝ)*r = n := by
      dsimp [r]
      field_simp
    rw [he,Nat.cast_smul_eq_nsmul]
  have hsqrt : CFC.sqrt D = positivePower A ((n : ℝ≥0)/(2*m)) := by
    rw [← complexPower_half_eq_sqrt D hD]
    have hc := complexPower_real_comp A r (1/2)
    change complexPower D (1/2) = complexPower A ((r : ℂ)*(1/2)) at hc
    rw [hc,positivePower_eq_complexPower A hA _ (by positivity)]
    congr 1
    dsimp [r]
    push_cast
    ring
  rw [hsm,hsqrt] at h
  exact h

theorem paperL_matrix_posDef {d} (n m : ℕ) (A B : Mat d) :
    (NormedSpace.exp (n • CFC.log A+m • CFC.log B)).PosDef := by
  let : NormedAlgebra ℚ (Mat d) := NormedAlgebra.restrictScalars ℚ ℝ (Mat d)
  have hs : IsSelfAdjoint (n • CFC.log A+m • CFC.log B) := by
    rw [isSelfAdjoint_iff]
    simp only [star_add,star_smul,star_trivial,IsSelfAdjoint.log.star_eq]
  exact (Matrix.nonneg_iff_posSemidef.mp hs.exp_nonneg).posDef_iff_isUnit.mpr
    (NormedSpace.isUnit_exp _)

theorem paperL_trace_real {d} (n m : ℕ) (A B : Mat d) :
    (NormedSpace.exp (n • CFC.log A+m • CFC.log B)).trace.im=0 :=
  hermitian_trace_im_zero _ (paperL_matrix_posDef n m A B).isHermitian

theorem paperL_trace_eq_real {d} (n m : ℕ) (A B : Mat d) :
    (NormedSpace.exp (n • CFC.log A+m • CFC.log B)).trace = (paperL n m A B : ℂ) := by
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im]
    exact paperL_trace_real n m A B

theorem paperL_nonneg {d} (n m : ℕ) (A B : Mat d) : 0 ≤ paperL n m A B :=
  (RCLike.nonneg_iff.mp (paperL_matrix_posDef n m A B).posSemidef.trace_nonneg).1

end RefinedBMV
