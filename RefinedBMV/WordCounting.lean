import RefinedBMV.PaperMain

namespace RefinedBMV

def countWords (k n : ℕ) : List Word := (allWords k).filter fun w => w.count false = n

theorem countWords_length (k n : ℕ) : (countWords k n).length = Nat.choose k n := by
  induction k generalizing n with
  | zero => cases n <;> simp [countWords, allWords]
  | succ k ih =>
    cases n with
    | zero =>
      simpa [countWords, allWords, List.filter_map, Function.comp_def, List.count_cons] using ih 0
    | succ n =>
      simpa [countWords, allWords, List.filter_map, Function.comp_def, List.count_cons,
        Nat.choose_succ_succ] using congrArg₂ (· + ·) (ih n) (ih (n+1))

theorem balancedWords_length (n m : ℕ) :
    (balancedWords n m).length = Nat.choose (n+m) n := countWords_length (n+m) n

theorem word_count_sum (w : Word) : w.count false + w.count true = w.length := by
  induction w with
  | nil => rfl
  | cons b w ih => cases b <;> simp <;> omega

theorem balancedWords_count_true (n m : ℕ) (w : Word) (hw : w ∈ balancedWords n m) :
    w.count true = m := by
  have h := mem_balancedWords n m w |>.mp hw
  have hsum := word_count_sum w
  omega

theorem evalWord_commute {d} (A B : Mat d) (hc : Commute A B) (w : Word) :
    evalWord A B w = A^(w.count false) * B^(w.count true) := by
  induction w with
  | nil => simp [evalWord]
  | cons b w ih =>
    cases b
    · simp [evalWord, ih, pow_succ', mul_assoc]
    · have hB : B * A^(w.count false) = A^(w.count false) * B :=
        (hc.pow_left _).eq.symm
      simp only [evalWord, ite_true, List.count_cons]
      simp
      rw [ih, ← mul_assoc, hB, mul_assoc, ← pow_succ']

theorem average_commute {d} (n m : ℕ) (A B : Mat d) (hc : Commute A B) :
    p n m A B = reTrace (A^n * B^m) := by
  let W := reTrace (A^n * B^m)
  have hw : ∀ w ∈ balancedWords n m, trWord A B w = W := by
    intro w hw
    have hn := (mem_balancedWords n m w).mp hw |>.2
    have hm := balancedWords_count_true n m w hw
    simp [trWord, evalWord_commute A B hc w, hn, hm, W]
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
  simp [hne, W]

end RefinedBMV
