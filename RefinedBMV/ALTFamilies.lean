import RefinedBMV.ALTInterpolationPath

namespace RefinedBMV
open Filter Topology Metric Set
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator NNReal
set_option maxHeartbeats 700000

theorem traceMoment_hermitian_product {d} (q : ℕ) (M N : Mat d)
    (hM : M.IsHermitian) (hN : N.IsHermitian) :
    traceMoment q (M*N) = reTrace ((M^2*N^2)^q) := by
  simp only [traceMoment,star_mul,Matrix.star_eq_conjTranspose,hM.eq,hN.eq]
  have he : N*M*(M*N) = N*(M^2*N) := by noncomm_ring
  rw [he,reTrace_mul_pow N (M^2*N) q]
  congr 2
  noncomm_ring

/-- ALT with integer total moment n and arbitrary positive integer q, first for positive definite inputs. -/
theorem alt_natural_posDef {d} (hdim : 0 < d) (A B : Mat d) (n q : ℕ)
    (hq : 0 < q) (hqn : q ≤ n) (hA : A.PosDef) (hB : B.PosDef) :
    reTrace ((A*B)^n) ≤ traceMoment q
      (complexPower A (((n : ℝ)/(2*q) : ℝ) : ℂ)*complexPower B (((n : ℝ)/(2*q) : ℝ) : ℂ)) := by
  have hq0 : 0 < q := hq
  have hn : 0 < n := lt_of_lt_of_le hq0 hqn
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq0
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let α : ℝ := (2*n : ℕ)/(2*(q : ℝ))
  let θ : ℝ := (q : ℝ)/n
  let M := complexPower A (1/2)*complexPower B (1/2)
  have hhalfA : (complexPower A (1/2)).PosDef := by simpa using complexPower_real_posDef A hA (1/2)
  have hhalfB : (complexPower B (1/2)).PosDef := by simpa using complexPower_real_posDef B hB (1/2)
  obtain ⟨U,P,hU,hP,hM,hPP⟩ := invertible_polar M (hhalfA.isUnit.mul hhalfB.isUnit)
  have hS : 0 < reTrace (P^(2*n)) := by
    let : NeZero d := ⟨by omega⟩
    exact (RCLike.pos_iff.mp (posDef_nat_pow P hP (2*n)).trace_pos).1
  let C := traceMoment q (complexPower A (((n : ℝ)/(2*q) : ℝ) : ℂ)*
    complexPower B (((n : ℝ)/(2*q) : ℝ) : ℂ))
  have hθ0 : 0 < θ := div_pos hqR hnR
  have hθ1 : θ ≤ 1 := (div_le_one₀ hnR).mpr (by exact_mod_cast hqn)
  have hα : 0 ≤ α := by dsimp [α]; positivity
  have hαθ : α*θ=1 := by dsimp [α,θ]; push_cast; field_simp
  have he : ((2*n : ℕ) : ℝ)/(4*q) = (n : ℝ)/(2*q) := by push_cast; ring
  have hl : ∀ z : ℂ, z.re = 0 → ‖altTracePath A B P U α (2*n) z‖ ≤ reTrace (P^(2*n)) := by
    intro z hz
    have hez : z = (z.im : ℂ)*Complex.I := by apply Complex.ext <;> simp [hz]
    rw [hez]
    exact altTracePath_left A B P U α (2*n) hP hU z.im
  have hr : ∀ z : ℂ, z.re = 1 → ‖altTracePath A B P U α (2*n) z‖^(2*q) ≤ C*(reTrace (P^(2*n)))^(2*q-1) := by
    intro z hz
    have hez : z = 1+(z.im : ℂ)*Complex.I := by apply Complex.ext <;> simp [hz]
    rw [hez]
    have h := altTracePath_right hdim A B P U (2*n) q hq hP hU z.im
    rw [he] at h
    exact h
  have h := moment_interpolation_scalar (altTracePath A B P U α (2*n)) (reTrace (P^(2*n))) C θ
    (2*q) hS (traceMoment_nonneg _ _) (by omega) hθ0 hθ1 (altTracePath_entire A B P U α (2*n))
    (altTracePath_bounded A B P U α (2*n) hα) hl hr
    (altTracePath_polar_point A B P U α θ (2*n) (by omega) hαθ hP hU hM)
  have hPS : reTrace (P^(2*n)) = reTrace ((A*B)^n) := by
    have hpow : P^(2*n) = (star M*M)^n := by rw [← hPP,← pow_two,← pow_mul]
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
    rw [← product_nat_trace_sandwich B A hB.posSemidef n,trace_mul_pow_complex B A n]
  rw [hPS] at h
  exact h

theorem alt_natural_psd {d} (hdim : 0 < d) (A B : Mat d) (n q : ℕ)
    (hq : 0 < q) (hqn : q ≤ n) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    reTrace ((A*B)^n) ≤ traceMoment q
      (positivePower A ((n : ℝ≥0)/(2*q))*positivePower B ((n : ℝ≥0)/(2*q))) := by
  have hq0 : 0 < q := hq
  have hn : 0 < n := lt_of_lt_of_le hq0 hqn
  let r : ℝ≥0 := (n : ℝ≥0)/(2*q)
  have hr : 0 < r := by dsimp [r]; positivity
  let Ap : ℝ → Mat d := fun t => A+t • (1 : Mat d)
  let Bp : ℝ → Mat d := fun t => B+t • (1 : Mat d)
  have hAt : Tendsto Ap (𝓝[>] (0 : ℝ)) (𝓝 A) := by
    have hc : Continuous Ap := by dsimp [Ap]; fun_prop
    simpa [Ap] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hBt : Tendsto Bp (𝓝[>] (0 : ℝ)) (𝓝 B) := by
    have hc : Continuous Bp := by dsimp [Bp]; fun_prop
    simpa [Bp] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hep : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  have hAp : ∀ᶠ t : ℝ in 𝓝[>] 0, (Ap t).PosDef := hep.mono (fun t ht => psd_add_eps_posDef A hA t ht)
  have hBp : ∀ᶠ t : ℝ in 𝓝[>] 0, (Bp t).PosDef := hep.mono (fun t ht => psd_add_eps_posDef B hB t ht)
  have hPA := positivePower_tendsto_of_psd hA r hAt (hAp.mono fun t ht => ht.posSemidef.nonneg)
  have hPB := positivePower_tendsto_of_psd hB r hBt (hBp.mono fun t ht => ht.posSemidef.nonneg)
  have hM := hPA.mul hPB
  have hL := reTrace_continuous.tendsto _ |>.comp ((hAt.mul hBt).pow n)
  have hR := reTrace_continuous.tendsto _ |>.comp ((hM.star.mul hM).pow q)
  apply le_of_tendsto_of_tendsto hL hR
  filter_upwards [hAp,hBp] with t htA htB
  have h := alt_natural_posDef hdim (Ap t) (Bp t) n q hq hqn htA htB
  change reTrace ((Ap t*Bp t)^n) ≤ traceMoment q (positivePower (Ap t) r*positivePower (Bp t) r)
  rw [positivePower_eq_complexPower _ htA r hr,positivePower_eq_complexPower _ htB r hr]
  simpa only [r,NNReal.coe_div,NNReal.coe_mul,NNReal.coe_natCast,NNReal.coe_ofNat] using h

/-- Equation (3.1) in its actual sandwich form for r=n/q, n≥q, and every positive integer q. -/
theorem alt_rational_sandwich_psd {d} (hdim : 0 < d) (X Y : Mat d) (n q : ℕ)
    (hq : 0 < q) (hqn : q ≤ n) (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    reTrace ((CFC.sqrt Y*X*CFC.sqrt Y)^n) ≤
      reTrace ((positivePower Y ((n : ℝ≥0)/(2*q))*positivePower X ((n : ℝ≥0)/q)*
        positivePower Y ((n : ℝ≥0)/(2*q)))^q) := by
  let r : ℝ≥0 := (n : ℝ≥0)/(2*q)
  have hn : 0 < n := lt_of_lt_of_le hq hqn
  have hr : 0 < r := by dsimp [r]; positivity
  let E := positivePower X r
  let F := positivePower Y r
  have hsE : star E=E := (positivePower_nonneg X r).isHermitian.eq
  have hsF : star F=F := (positivePower_nonneg Y r).isHermitian.eq
  have hEE : E*E = positivePower X ((n : ℝ≥0)/q) := by
    rw [positivePower_add X r r hr hr]
    have he : r+r = (n : ℝ≥0)/q := by dsimp [r]; ring
    rw [he]
  have h := alt_natural_psd hdim X Y n q hq hqn hX hY
  have hprod : star (E*F)*(E*F) = F*positivePower X ((n : ℝ≥0)/q)*F := by
    rw [star_mul,hsE,hsF]
    have he : F*E*(E*F)=F*(E*E)*F := by simp only [mul_assoc]
    rw [he,hEE]
  change reTrace ((X*Y)^n) ≤ traceMoment q (E*F) at h
  rw [traceMoment,hprod] at h
  have he : reTrace ((CFC.sqrt Y*X*CFC.sqrt Y)^n) = reTrace ((X*Y)^n) := by
    unfold reTrace
    rw [← product_nat_trace_sandwich Y X hY n,trace_mul_pow_complex Y X n]
  rw [he]
  exact h

/-- The complete integer-r ALT family required by the exponential bridge, for arbitrary q. -/
theorem alt_integer_psd {d} (hdim : 0 < d) (A B : Mat d) (k q : ℕ)
    (hk : 0 < k) (hq : 0 < q) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    reTrace ((A*B)^(k*q)) ≤ reTrace ((A^k*B^k)^q) := by
  have hq0 : 0 < q := hq
  have hqn : q ≤ k*q := by nlinarith
  have h := alt_natural_psd hdim A B (k*q) q hq hqn hA hB
  have he : ((k*q : ℕ) : ℝ≥0)/(2*q) = (k : ℝ≥0)/2 := by
    have hq' : (q : ℝ≥0) ≠ 0 := by exact_mod_cast hq0.ne'
    push_cast
    field_simp
  rw [he,traceMoment_hermitian_product _ _ _
    (positivePower_nonneg A _).isHermitian (positivePower_nonneg B _).isHermitian] at h
  have hpow (X : Mat d) (hX : X.PosSemidef) : (positivePower X ((k : ℝ≥0)/2))^2 = X^k := by
    rw [pow_two,positivePower_add X _ _ (by positivity) (by positivity)]
    have he : (k : ℝ≥0)/2+(k : ℝ≥0)/2 = k := by ring
    rw [he,positivePower_nat X hX k hk]
  rw [hpow A hA,hpow B hB] at h
  exact h

/-- Equation (3.1) for every positive integer r=k and q, in the manuscript's sandwich form. -/
theorem alt_integer_sandwich_psd {d} (hdim : 0 < d) (X Y : Mat d) (k q : ℕ)
    (hk : 0 < k) (hq : 0 < q) (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    reTrace ((CFC.sqrt Y*X*CFC.sqrt Y)^(k*q)) ≤
      reTrace ((positivePower Y ((k : ℝ≥0)/2)*X^k*positivePower Y ((k : ℝ≥0)/2))^q) := by
  have hqn : q ≤ k*q := by nlinarith
  have h := alt_rational_sandwich_psd hdim X Y (k*q) q hq hqn hX hY
  have hq' : (q : ℝ≥0) ≠ 0 := by exact_mod_cast hq.ne'
  have he : ((k*q : ℕ) : ℝ≥0)/q = k := by push_cast; field_simp
  have he2 : ((k*q : ℕ) : ℝ≥0)/(2*q) = (k : ℝ≥0)/2 := by push_cast; field_simp
  rw [he,he2,positivePower_nat X hX k hk] at h
  exact h

theorem positivePower_root_nat {d} (A : Mat d) (hA : A.PosSemidef) (k : ℕ) (hk : 0 < k) :
    (positivePower A (1/(k : ℝ≥0)))^k = A := by
  rw [← positivePower_nat _ (positivePower_nonneg A _) k hk]
  have hcomp := CFC.nnrpow_nnrpow (a := A) (x := 1/(k : ℝ≥0)) (y := (k : ℝ≥0))
  change positivePower (positivePower A (1/(k : ℝ≥0))) (k : ℝ≥0) =
    positivePower A ((1/(k : ℝ≥0))*(k : ℝ≥0)) at hcomp
  rw [hcomp,one_div_mul_cancel (by exact_mod_cast hk.ne' : (k : ℝ≥0) ≠ 0)]
  have h := positivePower_nat A hA 1 (by norm_num)
  simpa using h

theorem reTrace_sandwich_of_square {d} (S X Y : Mat d) (k : ℕ) (hSS : S*S=Y) :
    reTrace ((S*X*S)^k) = reTrace ((X*Y)^k) := by
  have he : S*X*S = S*(X*S) := by simp only [mul_assoc]
  rw [he,reTrace_mul_pow S (X*S) k]
  simp only [mul_assoc,hSS]

/-- The actual ALT inequality (3.2), for every positive k,m and including singular inputs.
Only the convergence of its left side remains for the exponential bridge. -/
theorem alt_trotter_approximants_le {d} (hdim : 0 < d) (D B : Mat d) (k m : ℕ)
    (hk : 0 < k) (hm : 0 < m) (hD : D.PosSemidef) (hB : B.PosSemidef) :
    reTrace ((positivePower D (1/(2*k))*positivePower B (1/(k : ℝ≥0))*
      positivePower D (1/(2*k)))^(m*k)) ≤ reTrace ((CFC.sqrt D*B*CFC.sqrt D)^m) := by
  let X := positivePower B (1/(k : ℝ≥0))
  let Y := positivePower D (1/(k : ℝ≥0))
  let S := positivePower D (1/(2*k))
  have h := alt_integer_psd hdim X Y k m hk hm (positivePower_nonneg B _) (positivePower_nonneg D _)
  have hSS : S*S=Y := by
    rw [positivePower_add D _ _ (by positivity) (by positivity)]
    have he : (1 : ℝ≥0)/(2*k)+1/(2*k) = 1/(k : ℝ≥0) := by ring
    rw [he]
  have hX : X^k=B := positivePower_root_nat B hB k hk
  have hY : Y^k=D := positivePower_root_nat D hD k hk
  rw [hX,hY] at h
  change reTrace ((S*X*S)^(m*k)) ≤ _
  rw [reTrace_sandwich_of_square S X Y (m*k) hSS,Nat.mul_comm m k]
  have he : reTrace ((B*D)^m) = reTrace ((CFC.sqrt D*B*CFC.sqrt D)^m) := by
    unfold reTrace
    rw [trace_mul_pow_complex B D m,product_nat_trace_sandwich D B hD m]
  rw [← he]
  exact h

end RefinedBMV
