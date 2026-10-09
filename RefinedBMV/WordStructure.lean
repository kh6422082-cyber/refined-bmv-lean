import RefinedBMV.WordCounting

namespace RefinedBMV

theorem allWords_nodup (k : ℕ) : (allWords k).Nodup := by
  induction k with
  | zero => simp [allWords]
  | succ k ih =>
    rw [allWords, List.nodup_append]
    refine ⟨ih.map (fun u v h => (List.cons.inj h).2),
      ih.map (fun u v h => (List.cons.inj h).2), ?_⟩
    intro a ha b hb hab
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp ha
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hb
    cases (List.cons.inj hab).1

theorem balancedWords_nodup (n m : ℕ) : (balancedWords n m).Nodup :=
  (allWords_nodup (n+m)).filter _

theorem balancedWords_reverse_mem (n m : ℕ) (w : Word) :
    w.reverse ∈ balancedWords n m ↔ w ∈ balancedWords n m := by
  simp [mem_balancedWords]

theorem balancedWords_reverse_perm (n m : ℕ) :
    ((balancedWords n m).map List.reverse).Perm (balancedWords n m) := by
  apply (List.perm_ext_iff_of_nodup
    ((balancedWords_nodup n m).map List.reverse_injective) (balancedWords_nodup n m)).mpr
  intro w
  constructor
  · intro hw
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw
    exact (balancedWords_reverse_mem n m v).mpr hv
  · intro hw
    exact List.mem_map.mpr ⟨w.reverse, (balancedWords_reverse_mem n m w).mpr hw, by simp⟩

theorem average_reversal (n m : ℕ) : (adj (average n m)).Perm (average n m) := by
  have hp := (balancedWords_reverse_perm n m).map
    (fun (w : Word) => ((1 / (Nat.choose (n+m) n : ℚ)), w))
  simpa only [adj, average, List.map_map, Function.comp_def] using hp

theorem complete_average_trace_real {d} (n m : ℕ) (A B : Mat d)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (evalPoly A B (average n m)).trace.im = 0 :=
  average_trace_real A B hA hB n m (average_reversal n m)

end RefinedBMV
