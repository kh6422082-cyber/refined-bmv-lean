import RefinedBMV.CubicALT

namespace RefinedBMV
open Filter Topology Metric Set
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 500000

noncomputable def cubicCenterMoment {d} (A B : Mat d) : ℝ :=
  reTrace ((CFC.sqrt (A^3)*CFC.sqrt (B^3))^2)

noncomputable def cubicMomentRatio {d} (A B : Mat d) : ℝ :=
  Real.sqrt (cubicCenterMoment A B/reTrace (A^3*B^3))

noncomputable def cubicMomentMargin {d} (A B : Mat d) : ℝ :=
  3*reTrace (A^3*B^3)*(1-cubicMomentRatio A B)^2*(1+cubicMomentRatio A B)/
    (3-cubicMomentRatio A B)

theorem normalized_midpoint_witness (D C a : ℝ) (hD : 0 < D) (ha : 0 ≤ a)
    (hC : C = D*a^2) : Real.sqrt (C/D) = a := by
  have he : C/D = a^2 := by rw [hC]; field_simp
  rw [he,Real.sqrt_sq ha]

theorem cubic_margin_posDef {d} (hdim : 0 < d) (A B : Mat d) (hA : A.PosDef) (hB : B.PosDef) :
    cubicMomentMargin A B ≤ reTrace (A^3*B^3)+2*reTrace (A^2*B*A*B^2)-3*cubicCenterMoment A B := by
  obtain ⟨a,ha0,ha1,hCa,hmargin⟩ := paper_cubic_quantitative_posDef hdim A B hA hB
  rw [← sqrt_cubic_eq_rpow A hA.posSemidef,← sqrt_cubic_eq_rpow B hB.posSemidef] at hCa hmargin
  have hD : 0 < reTrace (A^3*B^3) :=
    (cubic_center_pos hdim (A^3) (B^3) (posDef_nat_pow A hA 3) (posDef_nat_pow B hB 3)).trans_le
      (cubic_center_le_endpoint (A^3) (B^3) (hA.posSemidef.pow 3) (hB.posSemidef.pow 3))
  have hx : cubicMomentRatio A B = a := normalized_midpoint_witness _ _ a hD ha0 hCa
  simpa only [cubicMomentMargin,hx,cubicCenterMoment] using hmargin

/-- The center-ratio margin extends continuously even if the input matrices are singular. -/
theorem cubic_margin_psd {d} (hdim : 0 < d) (A B : Mat d) (hA : A.PosSemidef)
    (hB : B.PosSemidef) (hD : 0 < reTrace (A^3*B^3)) :
    cubicMomentMargin A B ≤ reTrace (A^3*B^3)+2*reTrace (A^2*B*A*B^2)-3*cubicCenterMoment A B := by
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
  have hCt : Tendsto (fun r => cubicCenterMoment (Ap r) (Bp r)) (𝓝[>] 0) (𝓝 (cubicCenterMoment A B)) :=
    reTrace_continuous.tendsto _ |>.comp ((hSA.mul hSB).pow 2)
  have hDt := reTrace_continuous.tendsto _ |>.comp ((hAt.pow 3).mul (hBt.pow 3))
  have hWt := reTrace_continuous.tendsto _ |>.comp ((((hAt.pow 2).mul hBt).mul hAt).mul (hBt.pow 2))
  have hxt : Tendsto (fun r => cubicMomentRatio (Ap r) (Bp r)) (𝓝[>] 0) (𝓝 (cubicMomentRatio A B)) :=
    (hCt.div hDt hD.ne').sqrt
  have hx1 : cubicMomentRatio A B ≤ 1 := by
    apply Real.sqrt_le_one.mpr
    apply (div_le_one₀ hD).mpr
    exact cubic_center_le_endpoint (A^3) (B^3) (hA.pow 3) (hB.pow 3)
  have hden : 3-cubicMomentRatio A B ≠ 0 := by linarith
  have ht1 : Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝[>] 0) (𝓝 1) := tendsto_const_nhds
  have ht2 : Tendsto (fun _ : ℝ => (2 : ℝ)) (𝓝[>] 0) (𝓝 2) := tendsto_const_nhds
  have ht3 : Tendsto (fun _ : ℝ => (3 : ℝ)) (𝓝[>] 0) (𝓝 3) := tendsto_const_nhds
  have hmt : Tendsto (fun r => cubicMomentMargin (Ap r) (Bp r)) (𝓝[>] 0) (𝓝 (cubicMomentMargin A B)) :=
    (((ht3.mul hDt).mul ((ht1.sub hxt).pow 2)).mul (ht1.add hxt)).div (ht3.sub hxt) hden
  have hrt := (hDt.add (ht2.mul hWt)).sub (ht3.mul hCt)
  apply le_of_tendsto_of_tendsto hmt hrt
  filter_upwards [hAp,hBp] with r hrA hrB
  exact cubic_margin_posDef hdim (Ap r) (Bp r) hrA hrB

/-- The complete quantitative PSD statement (7.2). -/
theorem paper_proposition_7_1_quantitative {d} (hdim : 0 < d) (A B : Mat d)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hD : 0 < reTrace (A^3*B^3)) :
    3*(reTrace ((CFC.rpow A (3/2)*CFC.rpow B (3/2))^2)-reTrace ((A*B)^3))+
      cubicMomentMargin A B ≤ reTrace (A^3*B^3)+2*reTrace (A^2*B*A*B^2)-3*reTrace ((A*B)^3) := by
  have h := cubic_margin_psd hdim A B hA hB hD
  unfold cubicCenterMoment at h
  rw [sqrt_cubic_eq_rpow A hA,sqrt_cubic_eq_rpow B hB] at h
  linarith only [h]

end RefinedBMV
