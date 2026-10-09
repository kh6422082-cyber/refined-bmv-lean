import RefinedBMV.TwoLetterMatrix
import RefinedBMV.TwoLetterWords

namespace RefinedBMV
open scoped ComplexOrder MatrixOrder NNReal
set_option maxHeartbeats 1000000

theorem reTrace_sandwich_square {d} (S B : Mat d) :
    reTrace ((S*B*S)^2) = reTrace (S^2*B*S^2*B) := by
  rw [pow_two]
  have he : S*B*S*(S*B*S) = (S*B*(S*S)*B)*S := by noncomm_ring
  rw [he, reTrace_cycle _ S]
  congr 1
  noncomm_ring

theorem quarter_power_square (a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    (a^((n : ℝ)/4))^2 = a^((n : ℝ)/2) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ha]
  congr 1
  ring

theorem diagonal_sandwich_target {d} (x : Fin d → ℝ) (hx : ∀ i, 0 ≤ x i)
    (B : Mat d) (hB : B.IsHermitian) (n : ℕ) :
    reTrace (((Matrix.diagonal (fun i => ((x i ^ ((n : ℝ)/4) : ℝ) : ℂ)) : Mat d) * B *
      Matrix.diagonal (fun i => ((x i ^ ((n : ℝ)/4) : ℝ) : ℂ)))^2) =
      ∑ i, ∑ j, Real.sqrt ((x i*x j)^n)*entrySquare (B i j) := by
  rw [reTrace_sandwich_square, diagonal_nat_power]
  have he : (fun i => (((x i^((n : ℝ)/4))^2 : ℝ) : ℂ)) =
      (fun i => ((x i^((n : ℝ)/2) : ℝ) : ℂ)) := by
    funext i
    rw [quarter_power_square _ (hx i) n]
  rw [he, diagonal_trace_two _ _ B hB]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [sqrt_nat_power _ (mul_nonneg (hx i) (hx j)), Real.mul_rpow (hx i) (hx j)]

theorem positivePower_spectral {d} (A : Mat d) (hA : A.PosSemidef)
    (r : ℝ≥0) (hr : 0 < r) :
    positivePower A r = Unitary.conjStarAlgAut ℂ (Mat d) hA.isHermitian.eigenvectorUnitary
      (Matrix.diagonal (fun i => ((hA.isHermitian.eigenvalues i ^ (r : ℝ) : ℝ) : ℂ))) := by
  have he := CFC.rpow_eq_cfc_real (a := A) (y := (r : ℝ)) hA.nonneg
  change CFC.rpow A (r : ℝ) = cfc (fun x : ℝ => x^(r : ℝ)) A at he
  rw [positivePower_eq_real_power A r hr, he, hA.isHermitian.cfc_eq]
  rfl

theorem unitary_conj_hermitian {d} (U : Matrix.unitaryGroup (Fin d) ℂ)
    (B : Mat d) (hB : B.IsHermitian) :
    (Unitary.conjStarAlgAut ℂ (Mat d) U B).IsHermitian := by
  change star (Unitary.conjStarAlgAut ℂ (Mat d) U B) = _
  rw [← map_star]
  change Unitary.conjStarAlgAut ℂ (Mat d) U B.conjTranspose = _
  rw [hB.eq]

theorem paperT_two_spectral {d} (A B : Mat d) (hA : A.PosSemidef)
    (hB : B.IsHermitian) (n : ℕ) (hn : 0 < n) :
    paperT n 2 A B =
      ∑ i, ∑ j, Real.sqrt ((hA.isHermitian.eigenvalues i*hA.isHermitian.eigenvalues j)^n)*
        entrySquare ((Unitary.conjStarAlgAut ℂ (Mat d)
          hA.isHermitian.eigenvectorUnitary).symm B i j) := by
  let U := hA.isHermitian.eigenvectorUnitary
  let f := Unitary.conjStarAlgAut ℂ (Mat d) U
  let B' := f.symm B
  let x := hA.isHermitian.eigenvalues
  let D : Mat d := Matrix.diagonal (fun i => ((x i^((n : ℝ)/4) : ℝ) : ℂ))
  have hB' : B'.IsHermitian := by
    change star (f.symm B) = f.symm B
    rw [← map_star]
    change f.symm B.conjTranspose = f.symm B
    rw [hB.eq]
  have hS : positivePower A ((n : ℝ≥0)/4) = f D := by
    rw [positivePower_spectral A hA _ (by positivity)]
    simp only [NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_ofNat]
    norm_num [f, U, D, x]
  have hBB : B = f B' := (f.apply_symm_apply B).symm
  unfold paperT
  norm_num only [Nat.cast_ofNat]
  rw [hS, hBB, ← map_mul, ← map_mul, ← map_pow]
  rw [Unitary.conjStarAlgAut_apply]
  rw [unitary_trace_conj]
  change reTrace ((D*B'*D)^2) = ∑ i, ∑ j,
    Real.sqrt ((x i*x j)^n)*entrySquare (f.symm (f B') i j)
  rw [f.symm_apply_apply]
  exact diagonal_sandwich_target x hA.eigenvalues_nonneg B' hB' n

theorem two_letter_word_ge_target {d} (A B : Mat d) (hA : A.PosSemidef)
    (hB : B.IsHermitian) (n : ℕ) (hn : 0 < n) (w : Word)
    (ha : w.count false = n) (hb : w.count true = 2) :
    paperT n 2 A B ≤ trWord A B w := by
  let U := hA.isHermitian.eigenvectorUnitary
  let f := Unitary.conjStarAlgAut ℂ (Mat d) U
  let x := hA.isHermitian.eigenvalues
  let D : Mat d := Matrix.diagonal (fun i => (x i : ℂ))
  let B' := f.symm B
  have hB' : B'.IsHermitian := by
    change star (f.symm B) = f.symm B
    rw [← map_star]
    change f.symm B.conjTranspose = f.symm B
    rw [hB.eq]
  have hAA : A = f D := hA.isHermitian.spectral_theorem
  have hBB : B = f B' := (f.apply_symm_apply B).symm
  have htr : trWord A B w = trWord D B' w := by
    rw [hAA, hBB]
    exact trWord_unitary_conj U D B' w
  obtain ⟨k,hk,he⟩ := two_true_gap_trace D B' n w ha hb
  rw [htr, he, paperT_two_spectral A B hA hB n hn]
  exact spectral_two_word_lower x hA.eigenvalues_nonneg B' hB' n k hk

/-- Proposition 3.2 with two B letters, for arbitrary positive degree and dimension.
The proof in fact only needs B Hermitian. -/
theorem paper_proposition_3_2_two {d} (A B : Mat d) (hA : A.PosSemidef)
    (hB : B.IsHermitian) (n : ℕ) (hn : 0 < n) : paperT n 2 A B ≤ p n 2 A B := by
  apply average_ge_of_words
  intro w hw
  exact two_letter_word_ge_target A B hA hB n hn w
    ((mem_balancedWords n 2 w).mp hw).2 (balancedWords_count_true n 2 w hw)

end RefinedBMV
