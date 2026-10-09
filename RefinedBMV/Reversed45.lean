import RefinedBMV.QuarticALTPath
import RefinedBMV.QuarticInterpolation

namespace RefinedBMV
open Filter Topology Metric Set
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator NNReal
set_option maxHeartbeats 600000

/-- The r=5/4,q=4 comparison, in its Schatten eighth-moment form. -/
theorem quartic_alt_posDef {d} (hdim : 0 < d) (A B : Mat d) (hA : A.PosDef) (hB : B.PosDef) :
    reTrace ((A*B)^5) ≤ hsEighth (complexPower A (5/8)*complexPower B (5/8)) := by
  let M := complexPower A (1/2)*complexPower B (1/2)
  have hhalfA : (complexPower A (1/2)).PosDef := by
    rw [complexPower_half_eq_sqrt A hA]
    exact Matrix.isStrictlyPositive_iff_posDef.mp (IsStrictlyPositive.sqrt A hA.isStrictlyPositive)
  have hhalfB : (complexPower B (1/2)).PosDef := by
    rw [complexPower_half_eq_sqrt B hB]
    exact Matrix.isStrictlyPositive_iff_posDef.mp (IsStrictlyPositive.sqrt B hB.isStrictlyPositive)
  obtain ⟨U,P,hU,hP,hM,hPP⟩ := invertible_polar M (hhalfA.isUnit.mul hhalfB.isUnit)
  have hS : 0 < reTrace (P^10) := by
    let : NeZero d := ⟨by omega⟩
    exact (RCLike.pos_iff.mp (posDef_nat_pow P hP 10).trace_pos).1
  let C := hsEighth (complexPower A (5/8)*complexPower B (5/8))
  have hleft : ∀ z : ℂ, z.re = 0 → ‖quarticALTPath A B P U z‖ ≤ reTrace (P^10) := by
    intro z hz
    have he : z = (z.im : ℂ)*Complex.I := by apply Complex.ext <;> simp [hz]
    rw [he]
    exact quarticALTPath_left_bound A B P U hP hU z.im
  have hright : ∀ z : ℂ, z.re = 1 → ‖quarticALTPath A B P U z‖^8 ≤ C*(reTrace (P^10))^7 := by
    intro z hz
    have he : z = 1+(z.im : ℂ)*Complex.I := by apply Complex.ext <;> simp [hz]
    rw [he]
    exact quarticALTPath_right_eighth_bound A B P U hP hU z.im
  have h := quartic_interpolation_scalar (quarticALTPath A B P U) (reTrace (P^10)) C hS
    (hsEighth_nonneg _) (quarticALTPath_entire A B P U) (quarticALTPath_bounded_strip A B P U)
    hleft hright (quarticALTPath_polar_point A B P U hP hU hM)
  have hPS : reTrace (P^10) = reTrace ((A*B)^5) := by
    have hpow : P^10 = (star M*M)^5 := by rw [← hPP]; noncomm_ring
    rw [hpow]
    dsimp only [M]
    rw [complexPower_half_eq_sqrt A hA,complexPower_half_eq_sqrt B hB,star_mul]
    have hsa : star (CFC.sqrt A) = CFC.sqrt A := by
      rw [← complexPower_half_eq_sqrt A hA]
      exact hhalfA.isHermitian.eq
    have hsb : star (CFC.sqrt B) = CFC.sqrt B := by
      rw [← complexPower_half_eq_sqrt B hB]
      exact hhalfB.isHermitian.eq
    rw [hsa,hsb]
    have he : CFC.sqrt B*CFC.sqrt A*(CFC.sqrt A*CFC.sqrt B) = CFC.sqrt B*A*CFC.sqrt B := by
      rw [mul_assoc,← mul_assoc (CFC.sqrt A) (CFC.sqrt A),CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg]
      simp only [mul_assoc]
    rw [he]
    unfold reTrace
    rw [← product_nat_trace_sandwich B A hB.posSemidef 5,trace_mul_pow_complex B A 5]
  rw [hPS] at h
  exact h

theorem complexPower_real_posDef {d} (A : Mat d) (hA : A.PosDef) (r : ℝ) :
    (complexPower A (r : ℂ)).PosDef := by
  have h := IsStrictlyPositive.rpow A r hA.isStrictlyPositive
  change IsStrictlyPositive (CFC.rpow A r) at h
  rw [complexPower_real A hA r]
  exact Matrix.isStrictlyPositive_iff_posDef.mp h

theorem complexPower_real_comp {d} (A : Mat d) (r : ℝ) (z : ℂ) :
    complexPower (complexPower A (r : ℂ)) z = complexPower A ((r : ℂ)*z) := by
  have hsm : (r : ℂ) • CFC.log A = r • CFC.log A := by
    ext i j
    simp only [Matrix.smul_apply,Complex.real_smul,smul_eq_mul]
  have hs : IsSelfAdjoint (r • CFC.log A) := (isSelfAdjoint_iff.mpr (star_trivial r)).smul .log
  have hl : CFC.log (complexPower A (r : ℂ)) = r • CFC.log A := by
    rw [complexPower,hsm,CFC.log_exp _ hs]
  change NormedSpace.exp (z • CFC.log (complexPower A (r : ℂ))) =
    NormedSpace.exp (((r : ℂ)*z) • CFC.log A)
  rw [hl,← hsm,smul_smul,mul_comm z]

theorem positivePower_eq_complexPower {d} (A : Mat d) (hA : A.PosDef) (r : ℝ≥0) (hr : 0 < r) :
    positivePower A r = complexPower A ((r : ℝ) : ℂ) := by
  rw [positivePower_eq_real_power A r hr,complexPower_real A hA (r : ℝ)]

theorem paperT45_posDef {d} (A B : Mat d) (hA : A.PosDef) :
    paperT 4 5 A B = reTrace ((complexPower A (4/5)*B)^5) := by
  norm_num [paperT]
  have hZ := positivePower_eq_complexPower A hA (2/5) (by norm_num)
  norm_num at hZ
  rw [hZ]
  have hZZ : complexPower A (2/5)*complexPower A (2/5) = complexPower A (4/5) := by
    rw [← complexPower_add]
    norm_num
  have h := reTrace_mul_pow (complexPower A (2/5)) (complexPower A (2/5)*B) 5
  simpa only [← mul_assoc,hZZ] using h.symm

/-- The oriented target comparison (3.4), first for positive inputs. -/
theorem reversed45_posDef {d} (hdim : 0 < d) (A B : Mat d) (hA : A.PosDef) (hB : B.PosDef) :
    paperT 4 5 A B ≤ paperT 5 4 B A := by
  let X := complexPower A (4/5)
  have hX : X.PosDef := by simpa using complexPower_real_posDef A hA (4/5)
  have h := quartic_alt_posDef hdim X B hX hB
  rw [paperT45_posDef A B hA]
  have hx : complexPower X (5/8) = complexPower A (1/2) := by
    have he := complexPower_real_comp A (4/5) (5/8)
    norm_num at he
    exact he
  have he : hsEighth (complexPower X (5/8)*complexPower B (5/8)) = paperT 5 4 B A := by
    rw [hx,hsEighth,star_mul,complexPower_star,complexPower_star]
    norm_num
    have hs : complexPower A (1/2)*complexPower A (1/2) = A := by
      rw [← complexPower_add]
      norm_num
      exact complexPower_one A hA
    have hprod : complexPower B (5/8)*complexPower A (1/2)*
        (complexPower A (1/2)*complexPower B (5/8)) =
        complexPower B (5/8)*A*complexPower B (5/8) := by
      rw [mul_assoc,← mul_assoc (complexPower A (1/2)) (complexPower A (1/2)),hs]
      simp only [mul_assoc]
    rw [hprod]
    norm_num [paperT]
    have hp := positivePower_eq_complexPower B hB (5/8) (by norm_num)
    norm_num at hp
    rw [hp]
  rw [he] at h
  exact h

theorem positivePower_tendsto_of_psd {d} {ι : Type*} {l : Filter ι} {f : ι → Mat d} {A : Mat d}
    (hA : A.PosSemidef) (r : ℝ≥0) (ht : Tendsto f l (𝓝 A)) (hf : ∀ᶠ i in l, 0 ≤ f i) :
    Tendsto (fun i => positivePower (f i) r) l (𝓝 (positivePower A r)) := by
  have hc := CFC.continuousOn_nnrpow (A := Mat d) r
  change ContinuousOn (fun M : Mat d => positivePower M r) {M | 0 ≤ M} at hc
  exact (hc A hA.nonneg).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨ht,hf⟩)

theorem reversed45_psd {d} (hdim : 0 < d) (A B : Mat d) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    paperT 4 5 A B ≤ paperT 5 4 B A := by
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
  have hPA := positivePower_tendsto_of_psd hA (2/5) hAt (hAp.mono fun r hr => hr.posSemidef.nonneg)
  have hPB := positivePower_tendsto_of_psd hB (5/8) hBt (hBp.mono fun r hr => hr.posSemidef.nonneg)
  have hL : Tendsto (fun r => paperT 4 5 (Ap r) (Bp r)) (𝓝[>] 0) (𝓝 (paperT 4 5 A B)) := by
    norm_num [paperT]
    exact reTrace_continuous.tendsto _ |>.comp (((hPA.mul hBt).mul hPA).pow 5)
  have hR : Tendsto (fun r => paperT 5 4 (Bp r) (Ap r)) (𝓝[>] 0) (𝓝 (paperT 5 4 B A)) := by
    norm_num [paperT]
    exact reTrace_continuous.tendsto _ |>.comp (((hPB.mul hAt).mul hPB).pow 4)
  apply le_of_tendsto_of_tendsto hL hR
  filter_upwards [hAp,hBp] with r hrA hrB
  exact reversed45_posDef hdim (Ap r) (Bp r) hrA hrB

/-- The strong (4,5) consequence, using the distinct oriented target comparison. -/
theorem paper_strong_4_5_psd {d} (hdim : 0 < d) (A B : Mat d)
    (hA : A.PosSemidef) (hB : B.PosSemidef) : paperT 4 5 A B ≤ p 4 5 A B := by
  have h54 := paper_theorem_2_2_psd B A hB hA.isHermitian
  have h45 := reversed45_psd hdim A B hA hB
  rw [p_letter_exchange 4 5 A B]
  exact (h45.trans h54.2.1).trans h54.1

end RefinedBMV
