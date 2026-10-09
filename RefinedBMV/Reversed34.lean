import RefinedBMV.ALTFamilies
import RefinedBMV.Strong43

namespace RefinedBMV
open Filter Topology Metric Set
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator NNReal
set_option maxHeartbeats 700000

theorem paperT34_posDef {d} (A B : Mat d) (hA : A.PosDef) :
    paperT 3 4 A B = reTrace ((complexPower A (3/4)*B)^4) := by
  norm_num [paperT]
  have hZ := positivePower_eq_complexPower A hA (3/8) (by norm_num)
  norm_num at hZ
  rw [hZ]
  have hZZ : complexPower A (3/8)*complexPower A (3/8) = complexPower A (3/4) := by
    rw [← complexPower_add]
    norm_num
  have h := reTrace_mul_pow (complexPower A (3/8)) (complexPower A (3/8)*B) 4
  simpa only [← mul_assoc,hZZ] using h.symm

/-- The remaining oriented target comparison (3.3), first for positive inputs. -/
theorem reversed34_posDef {d} (hdim : 0 < d) (A B : Mat d) (hA : A.PosDef) (hB : B.PosDef) :
    paperT 3 4 A B ≤ paperT 4 3 B A := by
  let X := complexPower A (3/4)
  have hX : X.PosDef := by simpa using complexPower_real_posDef A hA (3/4)
  have h := alt_natural_posDef hdim X B 4 3 (by norm_num) (by norm_num) hX hB
  norm_num at h
  rw [paperT34_posDef A B hA]
  have hx : complexPower X (2/3) = complexPower A (1/2) := by
    have he := complexPower_real_comp A (3/4) (2/3)
    norm_num at he
    exact he
  have he : traceMoment 3 (complexPower X (2/3)*complexPower B (2/3)) = paperT 4 3 B A := by
    rw [hx,traceMoment,star_mul,complexPower_star,complexPower_star]
    norm_num
    have hs : complexPower A (1/2)*complexPower A (1/2) = A := by
      rw [← complexPower_add]
      norm_num
      exact complexPower_one A hA
    have hprod : complexPower B (2/3)*complexPower A (1/2)*
        (complexPower A (1/2)*complexPower B (2/3)) =
        complexPower B (2/3)*A*complexPower B (2/3) := by
      rw [mul_assoc,← mul_assoc (complexPower A (1/2)) (complexPower A (1/2)),hs]
      simp only [mul_assoc]
    rw [hprod]
    norm_num [paperT]
    have hp := positivePower_eq_complexPower B hB (2/3) (by norm_num)
    norm_num at hp
    rw [hp]
  rw [he] at h
  exact h

theorem reversed34_psd {d} (hdim : 0 < d) (A B : Mat d) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    paperT 3 4 A B ≤ paperT 4 3 B A := by
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
  have hPA := positivePower_tendsto_of_psd hA (3/8) hAt (hAp.mono fun r hr => hr.posSemidef.nonneg)
  have hPB := positivePower_tendsto_of_psd hB (2/3) hBt (hBp.mono fun r hr => hr.posSemidef.nonneg)
  have hL : Tendsto (fun r => paperT 3 4 (Ap r) (Bp r)) (𝓝[>] 0) (𝓝 (paperT 3 4 A B)) := by
    norm_num [paperT]
    exact reTrace_continuous.tendsto _ |>.comp (((hPA.mul hBt).mul hPA).pow 4)
  have hR : Tendsto (fun r => paperT 4 3 (Bp r) (Ap r)) (𝓝[>] 0) (𝓝 (paperT 4 3 B A)) := by
    norm_num [paperT]
    exact reTrace_continuous.tendsto _ |>.comp (((hPB.mul hAt).mul hPB).pow 3)
  apply le_of_tendsto_of_tendsto hL hR
  filter_upwards [hAp,hBp] with r hrA hrB
  exact reversed34_posDef hdim (Ap r) (Bp r) hrA hrB

/-- The strong (3,4) consequence of the oriented ALT comparison and Proposition 4.1. -/
theorem paper_strong_3_4_psd {d} (hdim : 0 < d) (A B : Mat d)
    (hA : A.PosSemidef) (hB : B.PosSemidef) : paperT 3 4 A B ≤ p 3 4 A B := by
  have h43 := paper_proposition_4_1_psd hdim B A hB hA
  have h34 := reversed34_psd hdim A B hA hB
  rw [p_letter_exchange 3 4 A B]
  exact (h34.trans h43.2).trans h43.1

end RefinedBMV
