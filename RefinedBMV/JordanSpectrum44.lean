import RefinedBMV.Jordan44
import RefinedBMV.Equality54
import RefinedBMV.SchurTriangulation
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.Analysis.Complex.Polynomial.Basic

namespace RefinedBMV
open scoped ComplexOrder MatrixOrder
set_option maxHeartbeats 2000000

def entrySquare (z : ℂ) : ℝ := z.re^2 + z.im^2

theorem entrySquare_nonneg (z : ℂ) : 0 ≤ entrySquare z := add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem adj_mul_diag {d} (M : Mat d) (i : Fin d) :
    ((M.conjTranspose * M) i i).re = ∑ j, entrySquare (M j i) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  change (M j i).re * (M j i).re - (-(M j i).im) * (M j i).im =
    (M j i).re^2 + (M j i).im^2
  ring

theorem reTrace_adj_mul {d} (M : Mat d) :
    reTrace (M.conjTranspose * M) = ∑ i, ∑ j, entrySquare (M j i) := by
  simp only [reTrace, Matrix.trace, Complex.re_sum, Matrix.diag_apply]
  exact Finset.sum_congr rfl (fun i _ => adj_mul_diag M i)

theorem hermitian_diagonal_fourth_le {d} (H : Mat d) (hH : H.IsHermitian) :
    (∑ i, (H i i).re^4) ≤ reTrace (H^4) := by
  have hdiag (i : Fin d) : (H i i).re^2 ≤ ((H^2) i i).re := by
    have he : ((H^2) i i).re = ∑ j, entrySquare (H j i) := by
      simpa only [hH.eq, pow_two] using adj_mul_diag H i
    rw [he]
    calc
      (H i i).re^2 ≤ entrySquare (H i i) := le_add_of_nonneg_right (sq_nonneg _)
      _ ≤ ∑ j, entrySquare (H j i) :=
        Finset.single_le_sum (fun j _ => entrySquare_nonneg (H j i)) (Finset.mem_univ i)
  have hsq : (H^2).IsHermitian := hH.pow 2
  have he : reTrace (H^4) = ∑ i, ∑ j, entrySquare ((H^2) j i) := by
    have hx : (H^2).conjTranspose * H^2 = H^4 := by
      rw [hsq.eq]
      noncomm_ring
    rw [← hx]
    exact reTrace_adj_mul _
  rw [he]
  apply Finset.sum_le_sum
  intro i _
  calc
    (H i i).re^4 ≤ ((H^2) i i).re^2 := by
      have h := hdiag i
      have h0 := sq_nonneg (H i i).re
      nlinarith
    _ ≤ entrySquare ((H^2) i i) := le_add_of_nonneg_right (sq_nonneg _)
    _ ≤ ∑ j, entrySquare ((H^2) j i) :=
      Finset.single_le_sum (fun j _ => entrySquare_nonneg ((H^2) j i)) (Finset.mem_univ i)

theorem triangular_diag_mul {d} (M N : Mat d) (hM : M.IsUpperTriangular)
    (hN : N.IsUpperTriangular) (i : Fin d) : (M*N) i i = M i i * N i i := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_single i
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with hji | hij
    · rw [hM hji, zero_mul]
    · rw [hN hij, mul_zero]
  · intro h; exact False.elim (h (Finset.mem_univ i))

theorem triangular_diag_pow {d} (T : Mat d) (hT : T.IsUpperTriangular) (i : Fin d) (k : ℕ) :
    (T^k) i i = (T i i)^k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, triangular_diag_mul _ _ (hT.pow k) hT, ih, pow_succ]

theorem unitary_trace_conj {d} (U : Matrix.unitaryGroup (Fin d) ℂ) (M : Mat d) :
    reTrace ((U : Mat d) * M * star (U : Mat d)) = reTrace M := by
  rw [reTrace_cycle ((U : Mat d) * M) (star (U : Mat d)), ← mul_assoc]
  simp

theorem unitary_trace_conj_pow {d} (U : Matrix.unitaryGroup (Fin d) ℂ) (M : Mat d) (k : ℕ) :
    reTrace (((U : Mat d) * M * star (U : Mat d))^k) = reTrace (M^k) := by
  have hp := map_pow (Unitary.conjStarAlgAut ℂ (Mat d) U) M k
  rw [Unitary.conjStarAlgAut_apply, Unitary.conjStarAlgAut_apply] at hp
  rw [← hp]
  exact unitary_trace_conj U _

theorem unitary_charpoly_conj {d} (U : Matrix.unitaryGroup (Fin d) ℂ) (M : Mat d) :
    ((U : Mat d) * M * star (U : Mat d)).charpoly = M.charpoly := by
  rw [Matrix.charpoly_mul_comm ((U : Mat d) * M) (star (U : Mat d)), ← mul_assoc]
  simp

/-- A product with PSD left factor has the characteristic polynomial of a Hermitian sandwich.
This covers singular A directly and removes the regularization step from this proof. -/
theorem product_charpoly_sandwich {d} (A B : Mat d) (hA : A.PosSemidef) :
    (A*B).charpoly = (CFC.sqrt A * B * CFC.sqrt A).charpoly := by
  have hSS := CFC.sqrt_mul_sqrt_self A hA.nonneg
  calc
    (A*B).charpoly = (CFC.sqrt A * (CFC.sqrt A * B)).charpoly := by rw [← mul_assoc, hSS]
    _ = ((CFC.sqrt A * B) * CFC.sqrt A).charpoly := Matrix.charpoly_mul_comm _ _

theorem jordan_ge_product44 {d} (A B : Mat d) (hA : A.PosSemidef) (hB : B.IsHermitian) :
    reTrace ((A*B)^4) ≤ reTrace (((1/2 : ℝ) • (A*B+B*A))^4) := by
  let M := A*B
  let U := M.schurTriangulationUnitary
  let T : Mat d := M.schurTriangulation
  have hT : T.IsUpperTriangular := M.schurTriangulation.property
  have hM : M = (U : Mat d) * T * star (U : Mat d) := M.schur_triangulation
  let J := CFC.sqrt A * B * CFC.sqrt A
  have hS : (CFC.sqrt A).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian
  have hJ : J.IsHermitian := sandwich_isHermitian _ _ hS hB
  have hcp : T.charpoly = J.charpoly := by
    rw [← product_charpoly_sandwich A B hA]
    change T.charpoly = M.charpoly
    rw [hM, unitary_charpoly_conj]
  have hdiag (i : Fin d) : (T i i).im = 0 := by
    have hr : Polynomial.IsRoot T.charpoly (T i i) := by
      rw [Matrix.charpoly_of_isUpperTriangular T hT]
      simp only [Polynomial.IsRoot, Polynomial.eval_prod, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C]
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp
    rw [hcp] at hr
    have hm : T i i ∈ spectrum ℂ J := Matrix.mem_spectrum_iff_isRoot_charpoly.mpr hr
    rw [hJ.spectrum_eq_image_range] at hm
    obtain ⟨r, _, he⟩ := hm
    rw [← he]
    simp
  let K : Mat d := (1/2 : ℝ) • (T + T.conjTranspose)
  have hK : K.IsHermitian := by
    change K.conjTranspose = K
    simp [K, Matrix.conjTranspose_smul, add_comm]
  have hH : (1/2 : ℝ) • (A*B+B*A) = (U : Mat d) * K * star (U : Mat d) := by
    have hadj : B*A = M.conjTranspose := by
      dsimp [M]
      simp [Matrix.conjTranspose_mul, hA.isHermitian.eq, hB.eq]
    rw [hadj]
    change (1/2 : ℝ) • (M + M.conjTranspose) = _
    rw [hM]
    simp [K, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, smul_add, mul_add, add_mul,
      mul_assoc]
  have hp : reTrace ((A*B)^4) = ∑ i, (T i i).re^4 := by
    change reTrace (M^4) = _
    rw [hM, unitary_trace_conj_pow]
    simp only [reTrace, Matrix.trace, Complex.re_sum, Matrix.diag_apply,
      triangular_diag_pow T hT]
    apply Finset.sum_congr rfl
    intro i _
    have he : T i i = ((T i i).re : ℂ) := by apply Complex.ext <;> simp [hdiag i]
    rw [he]
    norm_cast
  rw [hp, hH, unitary_trace_conj_pow]
  have he (i : Fin d) : (K i i).re = (T i i).re := by
    simp [K, Complex.real_smul]
    ring
  simpa only [he] using hermitian_diagonal_fourth_le K hK

theorem strong44 {d} (A B : Mat d) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    reTrace (((1/2 : ℝ) • (A*B+B*A))^4) ≤ p 4 4 A B ∧
    reTrace ((A*B)^4) ≤ reTrace (((1/2 : ℝ) • (A*B+B*A))^4) ∧
    reTrace ((A*B)^4) = reTrace ((CFC.sqrt A * B * CFC.sqrt A)^4) := by
  refine ⟨p44_ge_jordan A B hA hB, jordan_ge_product44 A B hA hB.isHermitian, ?_⟩
  have he := reTrace_mul_pow (CFC.sqrt A) (CFC.sqrt A * B) 4
  simpa only [← mul_assoc, CFC.sqrt_mul_sqrt_self A hA.nonneg] using he

end RefinedBMV
