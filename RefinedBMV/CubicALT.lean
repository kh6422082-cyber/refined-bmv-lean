import RefinedBMV.CubicALTPath
import RefinedBMV.CubicInterpolation

namespace RefinedBMV
open Filter Topology Metric Set
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 600000

theorem complexPower_half_eq_sqrt {d} (A : Mat d) (hA : A.PosDef) :
    complexPower A (1/2) = CFC.sqrt A := by
  have he := complexPower_real A hA (1/2)
  norm_num at he
  have hs := CFC.sqrt_eq_rpow (a := A)
  change CFC.sqrt A = CFC.rpow A (1/2) at hs
  exact he.trans hs.symm

theorem cubicALTPath_polar_point {d} (A B P U : Mat d) (hP : P.PosDef)
    (hU : U ∈ unitary (Mat d))
    (hM : complexPower A (1/2)*complexPower B (1/2) = U*P) :
    ‖cubicALTPath A B P U (2/3)‖ = reTrace (P^6) := by
  have ha : (3 : ℂ)*(2/3)/4 = 1/2 := by norm_num
  have hp : (6 : ℂ)-3*(2/3)/2 = 5 := by norm_num
  have h5 := complexPower_nat P hP 5
  norm_num at h5
  rw [cubicALTPath,ha,hp,h5,hM]
  have he : U*P*P^5*star U = U*P^6*star U := by noncomm_ring
  rw [he,Matrix.trace_mul_comm (U*P^6) (star U),← mul_assoc,
    Unitary.star_mul_self_of_mem hU,one_mul]
  have hr : (P^6).trace = (reTrace (P^6) : ℂ) := by
    apply Complex.ext
    · rfl
    · simp only [Complex.ofReal_im]
      exact hermitian_trace_im_zero _ (hP.isHermitian.pow 6)
  have h0 : 0 ≤ reTrace (P^6) := (RCLike.nonneg_iff.mp (hP.posSemidef.pow 6).trace_nonneg).1
  rw [hr,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg h0]

theorem cubicALTPath_bounded_strip {d} (A B P U : Mat d) :
    ∃ K : ℝ, ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → ‖cubicALTPath A B P U z‖ ≤ K := by
  obtain ⟨CA,hCA,bA⟩ := complexPower_bounded_strip A 0 (3/4)
  obtain ⟨CB,hCB,bB⟩ := complexPower_bounded_strip B 0 (3/4)
  obtain ⟨CP,hCP,bP⟩ := complexPower_bounded_strip P (9/2) 6
  let tr : Mat d →L[ℂ] ℂ := (Matrix.traceLinearMap (Fin d) ℂ ℂ).toContinuousLinearMap
  refine ⟨‖tr‖*(CA*CB*CP*‖star U‖),?_⟩
  intro z hlo hhi
  have hrA : (3*z/4).re = 3*z.re/4 := by simp
  have hrP : (6-3*z/2).re = 6-3*z.re/2 := by simp
  have hAr := bA (3*z/4) (by rw [hrA]; linarith) (by rw [hrA]; linarith)
  have hBr := bB (3*z/4) (by rw [hrA]; linarith) (by rw [hrA]; linarith)
  have hPr := bP (6-3*z/2) (by rw [hrP]; linarith) (by rw [hrP]; linarith)
  have ht : ‖complexPower A (3*z/4)*complexPower B (3*z/4)*
      complexPower P (6-3*z/2)*star U‖ ≤ CA*CB*CP*‖star U‖ := by
    apply (norm_mul_le _ _).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply (norm_mul_le _ _).trans
    apply mul_le_mul ((norm_mul_le _ _).trans
      (mul_le_mul hAr hBr (norm_nonneg _) hCA)) hPr (norm_nonneg _) (mul_nonneg hCA hCB)
  exact (tr.le_opNorm _).trans (mul_le_mul_of_nonneg_left ht (norm_nonneg tr))

theorem hsFourth_hermitian_product {d} (M N : Mat d) (hM : M.IsHermitian) (hN : N.IsHermitian) :
    hsFourth (M*N) = reTrace ((M^2*N^2)^2) := by
  rw [hsFourth,star_mul,Matrix.star_eq_conjTranspose,Matrix.star_eq_conjTranspose,hM.eq,hN.eq]
  have he : (N*M*(M*N))^2 = N*((M*M)*(N*N)*(M*M))*N := by noncomm_ring
  rw [he,reTrace_cycle (N*((M*M)*(N*N)*(M*M))) N]
  have hr : N*(N*((M*M)*(N*N)*(M*M))) = (N^2*M^2)^2 := by noncomm_ring
  rw [hr,reTrace_mul_pow]

/-- The independent ALT comparison needed in (7.14), first for positive inputs. -/
theorem cubic_alt_posDef {d} (hdim : 0 < d) (A B : Mat d) (hA : A.PosDef) (hB : B.PosDef) :
    reTrace ((A*B)^3) ≤ reTrace ((CFC.sqrt (A^3)*CFC.sqrt (B^3))^2) := by
  let M := complexPower A (1/2)*complexPower B (1/2)
  have hhalfA : (complexPower A (1/2)).PosDef := by
    rw [complexPower_half_eq_sqrt A hA]
    exact Matrix.isStrictlyPositive_iff_posDef.mp (IsStrictlyPositive.sqrt A hA.isStrictlyPositive)
  have hhalfB : (complexPower B (1/2)).PosDef := by
    rw [complexPower_half_eq_sqrt B hB]
    exact Matrix.isStrictlyPositive_iff_posDef.mp (IsStrictlyPositive.sqrt B hB.isStrictlyPositive)
  obtain ⟨U,P,hU,hP,hM,hPP⟩ := invertible_polar M (hhalfA.isUnit.mul hhalfB.isUnit)
  have hS : 0 < reTrace (P^6) := by
    let : NeZero d := ⟨by omega⟩
    exact (RCLike.pos_iff.mp (posDef_nat_pow P hP 6).trace_pos).1
  let C := hsFourth (complexPower A (3/4)*complexPower B (3/4))
  have hleft : ∀ z : ℂ, z.re = 0 → ‖cubicALTPath A B P U z‖ ≤ reTrace (P^6) := by
    intro z hz
    have he : z = (z.im : ℂ)*Complex.I := by apply Complex.ext <;> simp [hz]
    rw [he]
    exact cubicALTPath_left_bound A B P U hP hU z.im
  have hright : ∀ z : ℂ, z.re = 1 → ‖cubicALTPath A B P U z‖^4 ≤ C*(reTrace (P^6))^3 := by
    intro z hz
    have he : z = 1+(z.im : ℂ)*Complex.I := by apply Complex.ext <;> simp [hz]
    rw [he]
    exact cubicALTPath_right_fourth_bound A B P U hP hU z.im
  have h := cubic_interpolation_scalar (cubicALTPath A B P U) (reTrace (P^6)) C hS
    (hsFourth_nonneg _) (cubicALTPath_entire A B P U) (cubicALTPath_bounded_strip A B P U)
    hleft hright (cubicALTPath_polar_point A B P U hP hU hM)
  have hPS : reTrace (P^6) = reTrace ((A*B)^3) := by
    have hpow : P^6 = (star M*M)^3 := by rw [← hPP]; noncomm_ring
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
    rw [← product_nat_trace_sandwich B A hB.posSemidef 3,trace_mul_pow_complex B A 3]
  have hC : C = reTrace ((CFC.sqrt (A^3)*CFC.sqrt (B^3))^2) := by
    have hqa : (complexPower A (3/4)).IsHermitian := by
      simpa using complexPower_real_hermitian A (3/4)
    have hqb : (complexPower B (3/4)).IsHermitian := by
      simpa using complexPower_real_hermitian B (3/4)
    have h2 (X : Mat d) (hX : X.PosDef) : (complexPower X (3/4))^2 = CFC.sqrt (X^3) := by
      rw [pow_two,← complexPower_add]
      norm_num
      have he := complexPower_nat_power X hX 3 (1/2)
      norm_num at he
      rw [← he,complexPower_half_eq_sqrt _ (posDef_nat_pow X hX 3)]
    dsimp only [C]
    rw [hsFourth_hermitian_product _ _ hqa hqb,h2 A hA,h2 B hB]
  rw [hPS,hC] at h
  exact h

/-- The cubic ALT comparison includes singular positive semidefinite inputs. -/
theorem cubic_alt_psd {d} (hdim : 0 < d) (A B : Mat d)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    reTrace ((A*B)^3) ≤ reTrace ((CFC.sqrt (A^3)*CFC.sqrt (B^3))^2) := by
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
  have hL := reTrace_continuous.tendsto _ |>.comp ((hAt.mul hBt).pow 3)
  have hR := reTrace_continuous.tendsto _ |>.comp ((hSA.mul hSB).pow 2)
  apply le_of_tendsto_of_tendsto hL hR
  filter_upwards [hAp,hBp] with r hrA hrB
  exact cubic_alt_posDef hdim (Ap r) (Bp r) hrA hrB

theorem paperT33 {d} (A B : Mat d) (hA : A.PosSemidef) :
    paperT 3 3 A B = reTrace ((A*B)^3) := by
  norm_num [paperT]
  rw [← sqrt_eq_positivePower]
  unfold reTrace
  rw [← product_nat_trace_sandwich A B hA 3]

/-- The complete PSD strong statement (7.1), with no assumed ALT arrow. -/
theorem paper_proposition_7_1_psd {d} (hdim : 0 < d) (A B : Mat d)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    3*reTrace ((CFC.rpow A (3/2)*CFC.rpow B (3/2))^2) ≤
      reTrace (A^3*B^3)+2*reTrace (A^2*B*A*B^2) ∧
    reTrace ((A*B)^3) ≤ reTrace ((CFC.rpow A (3/2)*CFC.rpow B (3/2))^2) ∧
    paperT 3 3 A B ≤ p 3 3 A B := by
  have hCS := cubic_alt_psd hdim A B hA hB
  have havg := cubic_average_ge_joint_moment hdim A B hA hB
  constructor
  · exact paper_cubic_joint_psd hdim A B hA hB
  constructor
  · simpa only [sqrt_cubic_eq_rpow A hA,sqrt_cubic_eq_rpow B hB] using hCS
  · rw [paperT33 A B hA]
    linarith only [hCS,havg]

end RefinedBMV
