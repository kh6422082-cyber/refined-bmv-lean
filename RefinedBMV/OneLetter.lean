import RefinedBMV.WordCounting

namespace RefinedBMV
open scoped ComplexOrder MatrixOrder NNReal

theorem average_eq_of_constant {d} (n m : ℕ) (A B : Mat d) (W : ℝ)
    (hw : ∀ w ∈ balancedWords n m, trWord A B w = W) : p n m A B = W := by
  have he : tracePoly A B (average n m) =
      (Nat.choose (n+m) n : ℝ)⁻¹ * (balancedWords n m).length * W := by
    unfold tracePoly average
    simp only [List.map_map, Function.comp_def]
    rw [List.map_congr_left (fun w hw' => by rw [hw w hw'])]
    simp
    ring
  have hp : 0 < Nat.choose (n+m) n := Nat.choose_pos (by omega)
  unfold p
  rw [← tracePoly_eq, he, balancedWords_length]
  have hne : (Nat.choose (n+m) n : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  simp [hne]

theorem no_true_replicate (w : Word) (hw : w.count true = 0) :
    w = List.replicate w.length false := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    cases b
    · have htail : w.count true = 0 := by simpa using hw
      simpa only [List.length_cons, List.replicate_succ] using congrArg (false :: ·) (ih htail)
    · simp at hw

theorem one_true_shape (w : Word) (hw : w.count true = 1) :
    ∃ r s : ℕ, w = List.replicate r false ++ [true] ++ List.replicate s false := by
  induction w with
  | nil => simp at hw
  | cons b w ih =>
    cases b
    · have htail : w.count true = 1 := by simpa using hw
      obtain ⟨r,s,he⟩ := ih htail
      refine ⟨r+1,s,?_⟩
      simp [he, List.replicate_succ]
    · have htail : w.count true = 0 := by simpa using hw
      refine ⟨0,w.length,?_⟩
      simp only [List.replicate_zero, List.nil_append, List.singleton_append]
      exact congrArg (true :: ·) (no_true_replicate w htail)

theorem evalWord_replicate_false {d} (A B : Mat d) (r : ℕ) :
    evalWord A B (List.replicate r false) = A^r := by
  induction r with
  | zero => rfl
  | succ r ih => simp [List.replicate_succ, evalWord, ih, pow_succ']

theorem one_true_trace {d} (A B : Mat d) (w : Word) (n : ℕ)
    (hn : w.count false = n) (hm : w.count true = 1) :
    trWord A B w = reTrace (A^n * B) := by
  obtain ⟨r,s,rfl⟩ := one_true_shape w hm
  have hrs : r+s = n := by simpa using hn
  simp only [trWord, evalWord_append, evalWord_replicate_false, evalWord,
    ite_true, mul_one]
  rw [reTrace_cycle (A^r * B) (A^s), ← mul_assoc, ← pow_add, Nat.add_comm s r, hrs]

theorem one_letter_average {d} (n : ℕ) (A B : Mat d) :
    p n 1 A B = reTrace (A^n * B) := by
  apply average_eq_of_constant
  intro w hw
  exact one_true_trace A B w n ((mem_balancedWords n 1 w).mp hw).2
    (balancedWords_count_true n 1 w hw)

theorem positivePower_nat {d} (A : Mat d) (hA : A.PosSemidef) (n : ℕ) (hn : 0 < n) :
    positivePower A (n : ℝ≥0) = A^n := by
  have hpos : 0 < (n : ℝ≥0) := by exact_mod_cast hn
  rw [positivePower_eq_real_power A _ hpos]
  exact CFC.rpow_natCast A n hA.nonneg

/-- Proposition 3.2: the complete one-B equality for every positive degree. -/
theorem paper_proposition_3_2_one {d} (n : ℕ) (hn : 0 < n) (A B : Mat d)
    (hA : A.PosSemidef) : p n 1 A B = paperT n 1 A B := by
  let S := positivePower A ((n : ℝ≥0)/2)
  have hpos : 0 < (n : ℝ≥0)/2 := by exact div_pos (by exact_mod_cast hn) (by norm_num)
  have hSS : S*S = A^n := by
    dsimp [S]
    rw [positivePower_add A _ _ hpos hpos]
    have he : (n : ℝ≥0)/2 + n/2 = n := by ring
    rw [he, positivePower_nat A hA n hn]
  rw [one_letter_average]
  simp only [paperT, Nat.cast_one, mul_one, pow_one]
  change reTrace (A^n*B) = reTrace (S*B*S)
  rw [reTrace_cycle (S*B) S, ← mul_assoc, hSS]

end RefinedBMV
