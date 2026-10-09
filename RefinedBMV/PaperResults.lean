import RefinedBMV.ExponentialBridge
import RefinedBMV.Reversed34
import RefinedBMV.TwoLetterBoundary

namespace RefinedBMV
open scoped ComplexOrder MatrixOrder
set_option maxHeartbeats 500000

def paperFinitePairs : Finset (ℕ × ℕ) := {(3,3),(4,3),(3,4),(4,4),(5,4),(4,5)}

def paperRegion (n m : ℕ) : Prop := min n m ≤ 2 ∨ (n,m) ∈ paperFinitePairs

/-- The complete six-pair PSD clause of Corollary 2.3. -/
theorem paper_corollary_2_3_finite_psd {d} (hdim : 0 < d) (n m : ℕ)
    (hpair : (n,m) ∈ paperFinitePairs) (A B : Mat d) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    paperT n m A B ≤ p n m A B := by
  simp only [paperFinitePairs,Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq] at hpair
  rcases hpair with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact (paper_proposition_7_1_psd hdim A B hA hB).2.2
  · have h := paper_proposition_4_1_psd hdim A B hA hB
    exact h.2.trans h.1
  · exact paper_strong_3_4_psd hdim A B hA hB
  · have h := paper_theorem_2_1_psd A B hA hB
    rw [← h.2.2]
    exact h.2.1.trans h.1
  · have h := paper_theorem_2_2_psd A B hA hB.isHermitian
    exact h.2.1.trans h.1
  · exact paper_strong_4_5_psd hdim A B hA hB

theorem paper_boundary_exponential_lower {d} (hdim : 0 < d) (n m : ℕ)
    (hn : 0 < n) (hm : 0 < m) (hm2 : m ≤ 2) (A B : Mat d) (hA : A.PosDef) (hB : B.PosDef) :
    paperL n m A B ≤ p n m A B := by
  have hT : paperT n m A B ≤ p n m A B := by
    have hcases : m=1 ∨ m=2 := by omega
    rcases hcases with rfl|rfl
    · exact (paper_proposition_3_2_one n hn A B hA.posSemidef).symm.le
    · exact paper_proposition_3_2_two A B hA.posSemidef hB.isHermitian n hn
  exact (paper_lemma_3_1 hdim n m hn hm A B hA hB).trans hT

/-- Corollary 2.3 on the exact union in (2.4), with arbitrary boundary degrees. -/
theorem paper_corollary_2_3 {d} (hdim : 0 < d) (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (hregion : paperRegion n m) (A B : Mat d) (hA : A.PosDef) (hB : B.PosDef) :
    paperL n m A B ≤ p n m A B := by
  rcases hregion with hboundary|hfinite
  · have hcases : n ≤ 2 ∨ m ≤ 2 := by omega
    rcases hcases with hn2|hm2
    · rw [p_letter_exchange n m A B,paperL_exchange n m A B]
      exact paper_boundary_exponential_lower hdim m n hm hn hn2 B A hB hA
    · exact paper_boundary_exponential_lower hdim n m hn hm hm2 A B hA hB
  · exact (paper_lemma_3_1 hdim n m hn hm A B hA hB).trans
      (paper_corollary_2_3_finite_psd hdim n m hfinite A B hA.posSemidef hB.posSemidef)

/-- The exponential endpoint equality in Theorem 2.2 and (6.7). -/
theorem paper_exponential_equality54 {d} (hdim : 0 < d) (A B : Mat d)
    (hA : A.PosDef) (hB : B.PosDef) : p 5 4 A B = paperL 5 4 A B ↔ Commute A B := by
  constructor
  · intro he
    have hS := paper_theorem_2_2_psd A B hA.posSemidef hB.isHermitian
    have hL := paper_lemma_3_1 hdim 5 4 (by norm_num) (by norm_num) A B hA hB
    have hPU : p 5 4 A B = reTrace (A*(A*B)^4) :=
      le_antisymm (by rw [he]; exact hL.trans hS.2.1) hS.1
    exact (equality54_iff_commute A B hA hB.isHermitian).mp hPU
  · intro hc
    have h := paper_commuting_equalities 5 4 (by norm_num) (by norm_num) A B hA hB hc
    exact h.1.trans h.2.2.symm

theorem paper_theorem_2_1_exponential {d} (hdim : 0 < d) (A B : Mat d)
    (hA : A.PosDef) (hB : B.PosDef) : paperL 4 4 A B ≤ p 4 4 A B := by
  have h := paper_theorem_2_1_psd A B hA.posSemidef hB.posSemidef
  have hT : paperT 4 4 A B ≤ p 4 4 A B := by rw [← h.2.2]; exact h.2.1.trans h.1
  exact (paper_lemma_3_1 hdim 4 4 (by norm_num) (by norm_num) A B hA hB).trans hT

/-- The full positive-input chain and equality clause of Theorem 2.2. -/
theorem paper_theorem_2_2_exponential {d} (hdim : 0 < d) (A B : Mat d)
    (hA : A.PosDef) (hB : B.PosDef) :
    reTrace (A*(A*B)^4) ≤ p 5 4 A B ∧
    paperT 5 4 A B ≤ reTrace (A*(A*B)^4) ∧
    paperL 5 4 A B ≤ paperT 5 4 A B ∧
    (p 5 4 A B = paperL 5 4 A B ↔ A*B=B*A) := by
  have h := paper_theorem_2_2_psd A B hA.posSemidef hB.isHermitian
  refine ⟨h.1,h.2.1,paper_lemma_3_1 hdim 5 4 (by norm_num) (by norm_num) A B hA hB,?_⟩
  simpa only [commute_iff_eq] using paper_exponential_equality54 hdim A B hA hB

end RefinedBMV
