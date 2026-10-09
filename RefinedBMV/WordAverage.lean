import RefinedBMV.LowDegree

namespace RefinedBMV
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem evalPoly_perm {d} (A B : Mat d) (p q : Poly) (hpq : p.Perm q) :
    evalPoly A B p = evalPoly A B q := by
  unfold evalPoly
  exact (hpq.map fun (t : ℚ × Word) => (t.1 : ℝ) • evalWord A B t.2).sum_eq

theorem reversal43 : (adj (average 4 3)).Perm (average 4 3) := by decide +kernel
theorem reversal44 : (adj (average 4 4)).Perm (average 4 4) := by decide +kernel
theorem reversal54 : (adj (average 5 4)).Perm (average 5 4) := by decide +kernel

theorem average_isHermitian_of_reversal {d} (A B : Mat d)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (n m : ℕ)
    (hr : (adj (average n m)).Perm (average n m)) :
    (evalPoly A B (average n m)).IsHermitian := by
  change (evalPoly A B (average n m)).conjTranspose = evalPoly A B (average n m)
  rw [← evalPoly_adj A B hA hB]
  exact evalPoly_perm A B _ _ hr

theorem average_trace_real {d} (A B : Mat d) (hA : A.IsHermitian)
    (hB : B.IsHermitian) (n m : ℕ)
    (hr : (adj (average n m)).Perm (average n m)) :
    (evalPoly A B (average n m)).trace.im = 0 := by
  have hh := average_isHermitian_of_reversal A B hA hB n m hr
  have ht := congrArg Matrix.trace hh.eq
  rw [Matrix.trace_conjTranspose] at ht
  have hi := congrArg Complex.im ht
  simp only [Complex.star_def, Complex.conj_im] at hi
  linarith

theorem count33 : (balancedWords 3 3).length = 20 := by decide +kernel
theorem nodup33 : (balancedWords 3 3).Nodup := by decide +kernel

def classified33 : Poly :=
  [(3/10, [false,false,false,true,true,true]),
   (6/10, [false,false,true,false,true,true]),
   (1/10, [false,true,false,true,false,true])]
def residual33 : Poly := add (average 3 3) (scale (-1) classified33)
theorem certificate33 : zeroCertificate residual33 := by decide +kernel

theorem identity33 {d} (A B : Mat d) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    p 3 3 A B =
      (3 * trWord A B [false,false,false,true,true,true] +
       6 * trWord A B [false,false,true,false,true,true] +
           trWord A B [false,true,false,true,false,true]) / 10 := by
  have h := tracePoly_zero_of_certificate A B hA hB residual33 certificate33
  rw [← tracePoly_eq] at h
  have ha : tracePoly A B (average 3 3) = p 3 3 A B := tracePoly_eq A B _
  have he : tracePoly A B residual33 = tracePoly A B (average 3 3) +
      tracePoly A B (scale (-1) classified33) := by
    simp [residual33, add, tracePoly]
  rw [he] at h
  rw [ha] at h
  norm_num [classified33, scale, tracePoly] at h
  linarith

end RefinedBMV
