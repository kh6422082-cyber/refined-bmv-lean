import RefinedBMV.TwoLetterScalar
import RefinedBMV.Reality

namespace RefinedBMV
open scoped ComplexOrder MatrixOrder
set_option maxHeartbeats 500000

theorem real_weight_entry_square (x y : ℝ) (z : ℂ) :
    ((x : ℂ)*z*(y : ℂ)*star z).re = x*y*entrySquare z := by
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im, entrySquare]
  ring

theorem hermitian_entry_swap {d} (B : Mat d) (hB : B.IsHermitian) (i j : Fin d) :
    B j i = star (B i j) := by
  exact (congrArg (fun M : Mat d => M j i) hB.eq).symm

theorem hermitian_entry_square_swap {d} (B : Mat d) (hB : B.IsHermitian) (i j : Fin d) :
    entrySquare (B j i) = entrySquare (B i j) := by
  rw [hermitian_entry_swap B hB]
  change (B i j).re^2 + (-(B i j).im)^2 = (B i j).re^2+(B i j).im^2
  ring

/-- The exact spectral entry expansion, retaining complex off-diagonal phases. -/
theorem diagonal_trace_two {d} (x y : Fin d → ℝ) (B : Mat d) (hB : B.IsHermitian) :
    reTrace (Matrix.diagonal (fun i => (x i : ℂ)) * B *
      Matrix.diagonal (fun i => (y i : ℂ)) * B) =
    ∑ i, ∑ j, x i * y j * entrySquare (B i j) := by
  simp only [reTrace, Matrix.trace, Matrix.diag_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.mul_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [hermitian_entry_swap B hB i j]
  exact real_weight_entry_square _ _ _

theorem diagonal_nat_power {d} (x : Fin d → ℝ) (k : ℕ) :
    (Matrix.diagonal (fun i => (x i : ℂ)) : Mat d)^k =
      Matrix.diagonal (fun i => (((x i)^k : ℝ) : ℂ)) := by
  rw [Matrix.diagonal_pow]
  apply congrArg Matrix.diagonal
  funext i
  simp only [Pi.pow_apply]
  norm_cast

theorem diagonal_word_two_trace {d} (x : Fin d → ℝ) (B : Mat d) (hB : B.IsHermitian)
    (r s : ℕ) :
    reTrace ((Matrix.diagonal (fun i => (x i : ℂ)) : Mat d)^r * B *
      (Matrix.diagonal (fun i => (x i : ℂ)) : Mat d)^s * B) =
      ∑ i, ∑ j, (x i)^r * (x j)^s * entrySquare (B i j) := by
  rw [diagonal_nat_power, diagonal_nat_power]
  exact diagonal_trace_two _ _ B hB

theorem spectral_two_word_lower {d} (x : Fin d → ℝ) (hx : ∀ i, 0 ≤ x i)
    (B : Mat d) (hB : B.IsHermitian) (n r : ℕ) (hr : r ≤ n) :
    (∑ i, ∑ j, Real.sqrt ((x i*x j)^n) * entrySquare (B i j)) ≤
      reTrace ((Matrix.diagonal (fun i => (x i : ℂ)) : Mat d)^r * B *
        (Matrix.diagonal (fun i => (x i : ℂ)) : Mat d)^(n-r) * B) := by
  rw [diagonal_word_two_trace x B hB]
  have he : (∑ i, ∑ j, (x i)^(n-r)*(x j)^r*entrySquare (B i j)) =
      ∑ i, ∑ j, (x i)^r*(x j)^(n-r)*entrySquare (B i j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hermitian_entry_square_swap B hB j i]
    ring
  have hs : (∑ i, ∑ j, 2*(Real.sqrt ((x i*x j)^n)*entrySquare (B i j))) ≤
      ∑ i, ∑ j, ((x i)^r*(x j)^(n-r)*entrySquare (B i j) +
        (x i)^(n-r)*(x j)^r*entrySquare (B i j)) := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    have h := mul_le_mul_of_nonneg_right
      (monomial_pair_lower (x i) (x j) (hx i) (hx j) n r hr) (entrySquare_nonneg (B i j))
    nlinarith only [h]
  simp only [← Finset.mul_sum, Finset.sum_add_distrib] at hs
  rw [he] at hs
  linarith

end RefinedBMV
