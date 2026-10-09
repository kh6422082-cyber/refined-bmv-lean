import RefinedBMV.WordStructure

namespace RefinedBMV

def swapWord (w : Word) : Word := w.map Bool.not

theorem swapWord_involutive (w : Word) : swapWord (swapWord w) = w := by
  simp [swapWord, List.map_map, Function.comp_def]

theorem swapWord_injective : Function.Injective swapWord := by
  intro u v h
  simpa only [swapWord_involutive] using congrArg swapWord h

theorem swapWord_count_false (w : Word) : (swapWord w).count false = w.count true := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    cases b
    · simpa [swapWord] using ih
    · simpa [swapWord] using ih

theorem swapWord_mem (n m : ℕ) (w : Word) :
    w ∈ balancedWords n m → swapWord w ∈ balancedWords m n := by
  intro hw
  apply (mem_balancedWords m n _).mpr
  have h := (mem_balancedWords n m w).mp hw
  refine ⟨by simpa [swapWord, Nat.add_comm] using h.1, ?_⟩
  rw [swapWord_count_false]
  exact balancedWords_count_true n m w hw

theorem balancedWords_swap_perm (n m : ℕ) :
    ((balancedWords n m).map swapWord).Perm (balancedWords m n) := by
  apply (List.perm_ext_iff_of_nodup
    ((balancedWords_nodup n m).map swapWord_injective) (balancedWords_nodup m n)).mpr
  intro w
  constructor
  · intro hw
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw
    exact swapWord_mem n m v hv
  · intro hw
    exact List.mem_map.mpr ⟨swapWord w, swapWord_mem m n w hw, swapWord_involutive w⟩

theorem evalWord_swap {d} (A B : Mat d) (w : Word) :
    evalWord B A (swapWord w) = evalWord A B w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    cases b
    · simpa [swapWord, evalWord] using congrArg (fun M => A*M) ih
    · simpa [swapWord, evalWord] using congrArg (fun M => B*M) ih

theorem trWord_swap {d} (A B : Mat d) (w : Word) :
    trWord B A (swapWord w) = trWord A B w := by rw [trWord, evalWord_swap]; rfl

/-- The first identity in (2.6), for every pair of degrees and every dimension. -/
theorem p_letter_exchange {d} (n m : ℕ) (A B : Mat d) : p n m A B = p m n B A := by
  have hco : Nat.choose (m+n) m = Nat.choose (n+m) n := by
    rw [Nat.choose_symm_add]
    rw [Nat.add_comm]
  have he := ((balancedWords_swap_perm n m).map
    (fun (w : Word) => ((1/(Nat.choose (n+m) n : ℚ)) : ℝ) * trWord B A w)).sum_eq
  have ht : tracePoly A B (average n m) = tracePoly B A (average m n) := by
    simpa [tracePoly, average, List.map_map, Function.comp_def, hco, trWord_swap] using he
  simpa only [tracePoly_eq, p] using ht

end RefinedBMV
