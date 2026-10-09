import RefinedBMV.CubicAnalytic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

namespace RefinedBMV
open Filter Topology Metric Set
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 500000

theorem posDef_nat_pow {d} (A : Mat d) (hA : A.PosDef) (k : ℕ) : (A^k).PosDef :=
  (hA.posSemidef.pow k).posDef_iff_isUnit.mpr (hA.isUnit.pow k)

theorem complexPower_nat {d} (A : Mat d) (hA : A.PosDef) (k : ℕ) :
    complexPower A (k : ℂ) = A^k := by
  let : NormedAlgebra ℚ (Mat d) := NormedAlgebra.restrictScalars ℚ ℝ (Mat d)
  unfold complexPower
  rw [Nat.cast_smul_eq_nsmul ℂ,NormedSpace.exp_nsmul,CFC.exp_log A hA.isStrictlyPositive]

theorem complexPower_nat_power {d} (A : Mat d) (hA : A.PosDef) (k : ℕ) (z : ℂ) :
    complexPower (A^k) z = complexPower A ((k : ℂ)*z) := by
  unfold complexPower
  rw [CFC.log_pow' k A hA.isStrictlyPositive,← Nat.cast_smul_eq_nsmul ℂ,smul_smul,mul_comm z]

theorem cubic_mixed_trace_reversal {d} (A B : Mat d) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    reTrace (A^2*B^2*A*B) = reTrace (A^2*B*A*B^2) := by
  rw [← reTrace_adj (A^2*B^2*A*B)]
  simp only [Matrix.conjTranspose_mul,hA.eq,hB.eq,(hA.pow 2).eq,(hB.pow 2).eq]
  have he : B*(A*(B^2*A^2)) = (B*A*B^2)*A^2 := by noncomm_ring
  rw [he,reTrace_cycle]
  simp only [mul_assoc]

theorem cubicStripTrace_cubic_specialization {d} (A B : Mat d) (hA : A.PosDef) (hB : B.PosDef) :
    (cubicStripTrace (A^3) (B^3) (2/3)).re = reTrace (A^2*B*A*B^2) := by
  have h23 (M : Mat d) (hM : M.PosDef) : complexPower (M^3) (2/3) = M^2 := by
    rw [complexPower_nat_power M hM 3]
    norm_num
    exact complexPower_nat M hM 2
  have h13 (M : Mat d) (hM : M.PosDef) : complexPower (M^3) (1/3) = M := by
    rw [complexPower_nat_power M hM 3]
    norm_num
    exact complexPower_one M hM
  have he : (1 : ℂ)-2/3 = 1/3 := by norm_num
  rw [cubicStripTrace,he,h23 A hA,h23 B hB,h13 A hA,h13 B hB]
  exact cubic_mixed_trace_reversal A B hA.isHermitian hB.isHermitian

/-- The unrestricted joint inequality (7.13), with the manuscript's actual matrix moments. -/
theorem cubic_matrix_joint_posDef {d} (hdim : 0 < d) (A B : Mat d) (hA : A.PosDef) (hB : B.PosDef) :
    3*reTrace ((CFC.sqrt (A^3)*CFC.sqrt (B^3))^2) ≤
      reTrace (A^3*B^3)+2*reTrace (A^2*B*A*B^2) := by
  have h := cubicStripTrace_joint_estimate hdim (A^3) (B^3) (posDef_nat_pow A hA 3) (posDef_nat_pow B hB 3)
  rw [cubic_midpoint_eq_sqrt (A^3) (B^3) (posDef_nat_pow A hA 3) (posDef_nat_pow B hB 3),
    cubicStripTrace_cubic_specialization A B hA hB] at h
  exact h

theorem psd_add_eps_posDef {d} (A : Mat d) (hA : A.PosSemidef) (r : ℝ) (hr : 0 < r) :
    (A+r • (1 : Mat d)).PosDef :=
  Matrix.PosDef.posSemidef_add hA (Matrix.PosDef.one.smul hr)

theorem sqrt_tendsto_of_psd {d} {ι : Type*} {l : Filter ι} {f : ι → Mat d} {A : Mat d}
    (hA : A.PosSemidef) (ht : Tendsto f l (𝓝 A)) (hf : ∀ᶠ i in l, 0 ≤ f i) :
    Tendsto (fun i => CFC.sqrt (f i)) l (𝓝 (CFC.sqrt A)) := by
  have hc : ContinuousOn (CFC.sqrt : Mat d → Mat d) {M | 0 ≤ M} := CFC.continuousOn_sqrt
  exact (hc A hA.nonneg).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨ht,hf⟩)

theorem reTrace_continuous {d} : Continuous (reTrace : Mat d → ℝ) := by
  let tr : Mat d →L[ℂ] ℂ := (Matrix.traceLinearMap (Fin d) ℂ ℂ).toContinuousLinearMap
  exact Complex.continuous_re.comp tr.continuous

/-- Singular inputs follow from genuine CFC continuity on the PSD cone. -/
theorem cubic_matrix_joint_psd {d} (hdim : 0 < d) (A B : Mat d)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    3*reTrace ((CFC.sqrt (A^3)*CFC.sqrt (B^3))^2) ≤
      reTrace (A^3*B^3)+2*reTrace (A^2*B*A*B^2) := by
  let Ap : ℝ → Mat d := fun r => A+r • (1 : Mat d)
  let Bp : ℝ → Mat d := fun r => B+r • (1 : Mat d)
  have hAt : Tendsto Ap (𝓝[>] (0 : ℝ)) (𝓝 A) := by
    have hc : Continuous Ap := by dsimp [Ap]; fun_prop
    simpa [Ap] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hBt : Tendsto Bp (𝓝[>] (0 : ℝ)) (𝓝 B) := by
    have hc : Continuous Bp := by dsimp [Bp]; fun_prop
    simpa [Bp] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hep : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r := self_mem_nhdsWithin
  have hAp : ∀ᶠ r : ℝ in 𝓝[>] 0, (Ap r).PosDef :=
    hep.mono (fun r hr => psd_add_eps_posDef A hA r hr)
  have hBp : ∀ᶠ r : ℝ in 𝓝[>] 0, (Bp r).PosDef :=
    hep.mono (fun r hr => psd_add_eps_posDef B hB r hr)
  have hSA := sqrt_tendsto_of_psd (hA.pow 3) (hAt.pow 3)
    (hAp.mono fun r hr => (hr.posSemidef.pow 3).nonneg)
  have hSB := sqrt_tendsto_of_psd (hB.pow 3) (hBt.pow 3)
    (hBp.mono fun r hr => (hr.posSemidef.pow 3).nonneg)
  have hL := (tendsto_const_nhds (x := (3 : ℝ))).mul
    (reTrace_continuous.tendsto _ |>.comp ((hSA.mul hSB).pow 2))
  have hD := reTrace_continuous.tendsto _ |>.comp ((hAt.pow 3).mul (hBt.pow 3))
  have hW := reTrace_continuous.tendsto _ |>.comp ((((hAt.pow 2).mul hBt).mul hAt).mul (hBt.pow 2))
  have hR := hD.add ((tendsto_const_nhds (x := (2 : ℝ))).mul hW)
  apply le_of_tendsto_of_tendsto hL hR
  filter_upwards [hAp,hBp] with r hrA hrB
  exact cubic_matrix_joint_posDef hdim (Ap r) (Bp r) hrA hrB

/-- An unconditional intermediate assembly with the complete 20-word average.
The separate cubic ALT module completes its comparison with Tr(AB)^3. -/
theorem cubic_average_ge_joint_moment {d} (hdim : 0 < d) (A B : Mat d)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (9*reTrace ((CFC.sqrt (A^3)*CFC.sqrt (B^3))^2)+reTrace ((A*B)^3))/10 ≤ p 3 3 A B := by
  have hj := cubic_matrix_joint_psd hdim A B hA hB
  have he := cubic_average_deficit A B hA.isHermitian hB.isHermitian
  linarith

theorem sqrt_cubic_eq_rpow {d} (A : Mat d) (hA : A.PosSemidef) :
    CFC.sqrt (A^3) = CFC.rpow A (3/2) := by
  rw [← positivePower_nat A hA 3 (by norm_num),sqrt_positivePower,
    positivePower_eq_real_power A _ (by norm_num)]
  norm_num

/-- The PSD joint estimate in the real-power notation used in (7.13). -/
theorem paper_cubic_joint_psd {d} (hdim : 0 < d) (A B : Mat d)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    3*reTrace ((CFC.rpow A (3/2)*CFC.rpow B (3/2))^2) ≤
      reTrace (A^3*B^3)+2*reTrace (A^2*B*A*B^2) := by
  simpa only [sqrt_cubic_eq_rpow A hA,sqrt_cubic_eq_rpow B hB] using
    cubic_matrix_joint_psd hdim A B hA hB

/-- The quantitative matrix margin in (7.13), before the independent ALT comparison. -/
theorem paper_cubic_quantitative_posDef {d} (hdim : 0 < d) (A B : Mat d)
    (hA : A.PosDef) (hB : B.PosDef) :
    ∃ a : ℝ, 0 ≤ a ∧ a ≤ 1 ∧
      reTrace ((CFC.rpow A (3/2)*CFC.rpow B (3/2))^2) = reTrace (A^3*B^3)*a^2 ∧
      3*reTrace (A^3*B^3)*(1-a)^2*(1+a)/(3-a) ≤
        reTrace (A^3*B^3)+2*reTrace (A^2*B*A*B^2)-
          3*reTrace ((CFC.rpow A (3/2)*CFC.rpow B (3/2))^2) := by
  have hAp := posDef_nat_pow A hA 3
  have hBp := posDef_nat_pow B hB 3
  obtain ⟨a,ha0,ha1,hC,hW⟩ := cubicStripTrace_point_ratio_bound hdim (A^3) (B^3) hAp hBp
  rw [cubic_midpoint_eq_sqrt (A^3) (B^3) hAp hBp] at hC
  change reTrace ((CFC.sqrt (A^3)*CFC.sqrt (B^3))^2) = _ at hC
  rw [sqrt_cubic_eq_rpow A hA.posSemidef,sqrt_cubic_eq_rpow B hB.posSemidef] at hC
  rw [cubicStripTrace_cubic_specialization A B hA hB] at hW
  have hD : 0 ≤ reTrace (A^3*B^3) :=
    (cubic_center_pos hdim (A^3) (B^3) hAp hBp).le.trans
      (cubic_center_le_endpoint (A^3) (B^3) hAp.posSemidef hBp.posSemidef)
  exact ⟨a,ha0,ha1,hC,(cubic_joint_of_ratio_bound _ _ _ a hD ha0 ha1 hC hW).1⟩

theorem product_nat_trace_sandwich {d} (A B : Mat d) (hA : A.PosSemidef) (k : ℕ) :
    ((A*B)^k).trace = ((CFC.sqrt A*B*CFC.sqrt A)^k).trace := by
  have h := trace_mul_pow_complex (CFC.sqrt A) (CFC.sqrt A*B) k
  simpa only [← mul_assoc,CFC.sqrt_mul_sqrt_self A hA.nonneg] using h

/-- In particular the cubic S in (7.14)-(7.15) is a real trace, not just a real part. -/
theorem product_nat_trace_real {d} (A B : Mat d) (hA : A.PosSemidef)
    (hB : B.IsHermitian) (k : ℕ) : ((A*B)^k).trace.im = 0 := by
  have hs : (CFC.sqrt A).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian
  rw [product_nat_trace_sandwich A B hA k]
  exact hermitian_trace_im_zero _ ((sandwich_isHermitian _ _ hs hB).pow k)

theorem product_nat_trace_nonneg {d} (A B : Mat d) (hA : A.PosSemidef)
    (hB : B.PosSemidef) (k : ℕ) : 0 ≤ reTrace ((A*B)^k) := by
  have hs : (CFC.sqrt A).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian
  have hp : (CFC.sqrt A*B*CFC.sqrt A).PosSemidef := by
    simpa only [hs.eq] using hB.mul_mul_conjTranspose_same (CFC.sqrt A)
  unfold reTrace
  rw [product_nat_trace_sandwich A B hA k]
  exact (RCLike.nonneg_iff.mp (hp.pow k).trace_nonneg).1

end RefinedBMV
