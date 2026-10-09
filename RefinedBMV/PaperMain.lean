import RefinedBMV.JordanSpectrum44
import RefinedBMV.WordAverage

namespace RefinedBMV
open scoped ComplexOrder MatrixOrder NNReal

/-- The oriented moment (2.1). Statements about this quantity require m > 0. -/
noncomputable def paperT {d} (n m : ℕ) (A B : Mat d) : ℝ :=
  reTrace ((positivePower A ((n : ℝ≥0) / (2 * m)) * B *
    positivePower A ((n : ℝ≥0) / (2 * m)))^m)

theorem positivePower_eq_real_power {d} (A : Mat d) (r : ℝ≥0) (hr : 0 < r) :
    positivePower A r = CFC.rpow A (r : ℝ) := CFC.nnrpow_eq_rpow hr

theorem paperT44 {d} (A B : Mat d) :
    paperT 4 4 A B = reTrace ((CFC.sqrt A * B * CFC.sqrt A)^4) := by
  norm_num [paperT]
  rw [← sqrt_eq_positivePower]

theorem paperT54 {d} (A B : Mat d) :
    paperT 5 4 A B = reTrace ((CFC.rpow A (5/8) * B * CFC.rpow A (5/8))^4) := by
  norm_num [paperT]
  rw [positivePower_eq_real_power A _ (by norm_num)]
  norm_num

/-- Theorem 2.1, the complete three-arrow PSD statement (2.2). -/
theorem paper_theorem_2_1_psd {d} (A B : Mat d) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    reTrace (((1/2 : ℝ) • (A*B+B*A))^4) ≤ p 4 4 A B ∧
    reTrace ((A*B)^4) ≤ reTrace (((1/2 : ℝ) • (A*B+B*A))^4) ∧
    reTrace ((A*B)^4) = paperT 4 4 A B := by
  rw [paperT44]
  exact strong44 A B hA hB

/-- Theorem 2.2, the complete PSD/Hermitian strong chain (2.3). -/
theorem paper_theorem_2_2_psd {d} (A B : Mat d) (hA : A.PosSemidef) (hB : B.IsHermitian) :
    reTrace (A*(A*B)^4) ≤ p 5 4 A B ∧
    paperT 5 4 A B ≤ reTrace (A*(A*B)^4) ∧ 0 ≤ paperT 5 4 A B := by
  have h := strong54 A B hA hB
  norm_num [paperT]
  exact h

/-- Theorem 2.2, the complete positive-A equality classification for P=U. -/
theorem paper_theorem_2_2_equality {d} (A B : Mat d) (hA : A.PosDef) (hB : B.IsHermitian) :
    p 5 4 A B = reTrace (A*(A*B)^4) ↔ A*B = B*A := by
  simpa only [commute_iff_eq] using equality54_iff_commute A B hA hB

end RefinedBMV
