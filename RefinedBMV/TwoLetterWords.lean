import RefinedBMV.OneLetter
import RefinedBMV.WordStructure

namespace RefinedBMV
set_option maxHeartbeats 2000000

theorem two_true_shape (w : Word) (hw : w.count true = 2) :
    ∃ r s t : ℕ, w = List.replicate r false ++ [true] ++ List.replicate s false ++
      [true] ++ List.replicate t false := by
  induction w with
  | nil => simp at hw
  | cons b w ih =>
    cases b
    · have htail : w.count true = 2 := by simpa using hw
      obtain ⟨r,s,t,he⟩ := ih htail
      refine ⟨r+1,s,t,?_⟩
      simp [he, List.replicate_succ]
    · have htail : w.count true = 1 := by simpa using hw
      obtain ⟨s,t,he⟩ := one_true_shape w htail
      refine ⟨0,s,t,?_⟩
      simpa using congrArg (true :: ·) he

/-- Every two-B trace is one cyclic gap trace; no numerical or finite-degree cutoff. -/
theorem two_true_gap_trace {d} (A B : Mat d) (n : ℕ) (w : Word)
    (hn : w.count false = n) (hm : w.count true = 2) :
    ∃ k ≤ n, trWord A B w = reTrace (A^k * B * A^(n-k) * B) := by
  obtain ⟨r,s,t,rfl⟩ := two_true_shape w hm
  have hsum : r+s+t = n := by simpa [Nat.add_assoc] using hn
  refine ⟨r+t, by omega, ?_⟩
  have hex : evalWord A B (List.replicate r false ++ [true] ++ List.replicate s false ++
      [true] ++ List.replicate t false) = A^r * B * A^s * B * A^t := by
    simp [evalWord_append, evalWord_replicate_false, evalWord, mul_assoc]
  rw [trWord, hex, reTrace_cycle (A^r * B * A^s * B) (A^t)]
  have hk : n-(r+t) = s := by omega
  rw [hk]
  have hp : A^t * A^r = A^(r+t) := by rw [← pow_add, Nat.add_comm t r]
  simp only [← mul_assoc, hp]

theorem evalWord_hom {d} (f : Mat d →+* Mat d) (A B : Mat d) (w : Word) :
    evalWord (f A) (f B) w = f (evalWord A B w) := by
  induction w with
  | nil => simp [evalWord]
  | cons b w ih => cases b <;> simp [evalWord, ih]

theorem trWord_unitary_conj {d} (U : Matrix.unitaryGroup (Fin d) ℂ) (A B : Mat d) (w : Word) :
    trWord (Unitary.conjStarAlgAut ℂ (Mat d) U A)
      (Unitary.conjStarAlgAut ℂ (Mat d) U B) w = trWord A B w := by
  unfold trWord
  have he := evalWord_hom (Unitary.conjStarAlgAut ℂ (Mat d) U).toRingHom A B w
  change evalWord (Unitary.conjStarAlgAut ℂ (Mat d) U A)
    (Unitary.conjStarAlgAut ℂ (Mat d) U B) w =
    Unitary.conjStarAlgAut ℂ (Mat d) U (evalWord A B w) at he
  rw [he]
  rw [Unitary.conjStarAlgAut_apply]
  exact unitary_trace_conj U _

theorem list_constant_lower (l : List Word) (f : Word → ℝ) (c T : ℝ) (hc : 0 ≤ c)
    (hf : ∀ w ∈ l, T ≤ f w) :
    (l.map fun _ => c*T).sum ≤ (l.map fun w => c*f w).sum := by
  induction l with
  | nil => simp
  | cons w l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (mul_le_mul_of_nonneg_left (hf w (by simp)) hc)
      (ih (fun z hz => hf z (by simp [hz])))

theorem average_ge_of_words {d} (n m : ℕ) (A B : Mat d) (T : ℝ)
    (hw : ∀ w ∈ balancedWords n m, T ≤ trWord A B w) : T ≤ p n m A B := by
  let c : ℝ := ((1/(Nat.choose (n+m) n : ℚ)) : ℝ)
  have hp : 0 < Nat.choose (n+m) n := Nat.choose_pos (by omega)
  have hn : (Nat.choose (n+m) n : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hs := list_constant_lower (balancedWords n m) (trWord A B) c T hc hw
  have he : ((balancedWords n m).map fun _ => c*T).sum = T := by
    simp [c, balancedWords_length]
    field_simp
  rw [he] at hs
  unfold p
  rw [← tracePoly_eq]
  simpa [tracePoly, average, List.map_map, Function.comp_def, c] using hs

end RefinedBMV
