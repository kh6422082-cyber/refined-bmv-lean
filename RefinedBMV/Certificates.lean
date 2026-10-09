import RefinedBMV.Core

namespace RefinedBMV
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

-- All binary position words, before imposing the two multiplicities.
def allWords : ℕ → List Word
  | 0 => [[]]
  | k+1 => (allWords k).map (false :: ·) ++ (allWords k).map (true :: ·)
def balancedWords (n m : ℕ) : List Word :=
  (allWords (n+m)).filter fun w => w.count false = n
def average (n m : ℕ) : Poly :=
  (balancedWords n m).map fun w => (1 / (Nat.choose (n+m) n : ℚ), w)

theorem mem_allWords (k : ℕ) (w : Word) : w ∈ allWords k ↔ w.length = k := by
  induction k generalizing w with
  | zero => simp [allWords]
  | succ k ih =>
    cases w with
    | nil => simp [allWords]
    | cons b w => cases b <;> simp [allWords, ih]

theorem mem_balancedWords (n m : ℕ) (w : Word) :
    w ∈ balancedWords n m ↔ w.length = n+m ∧ w.count false = n := by
  simp [balancedWords, mem_allWords]

theorem count43 : (balancedWords 4 3).length = 35 := by decide +kernel
theorem count44 : (balancedWords 4 4).length = 70 := by decide +kernel
theorem count54 : (balancedWords 5 4).length = 126 := by decide +kernel
theorem nodup43 : (balancedWords 4 3).Nodup := by decide +kernel
theorem nodup44 : (balancedWords 4 4).Nodup := by decide +kernel
theorem nodup54 : (balancedWords 5 4).Nodup := by decide +kernel

def l43 : Poly := add (atom [false, false, true]) (scale (-1) (atom [false, true, false]))
def r43 : Poly := add (atom [false, true, false]) (scale (-1) (atom [true, false, false]))
def rhs43 : Poly := add (weightedSquare (add (l43) (scale (2) (r43))) [] [true]) (weightedSquare (r43) [] [true])
def residual43 : Poly := add (scale (5) (add (average 4 3) (scale (-1) (atom [false, false, true, false, true, false, true])))) (scale (-1) (rhs43))
theorem certificate43 : zeroCertificate residual43 := by decide +kernel
def u1 : Poly := atom [false, false, true, true]
def u2 : Poly := atom [false, true, false, true]
def u3 : Poly := atom [false, true, true, false]
def u4 : Poly := atom [true, false, false, true]
def u5 : Poly := atom [true, false, true, false]
def u6 : Poly := atom [true, true, false, false]
def v1 : Poly := add (u1) (add (u2) (scale (-2) (u3)))
def v2 : Poly := add (u4) (scale (-1) (u3))
def v3 : Poly := add (u5) (scale (-1) (u3))
def v4 : Poly := add (u6) (scale (-1) (u3))
def w1 : Poly := add (v1) (add (v2) (scale (-1) (v3)))
def w2 : Poly := add (v2) (add (scale (-7/6) (v3)) (scale (-1/4) (v4)))
def w3 : Poly := add (v3) (scale (3/10) (v4))
def w4 : Poly := v4
def rhs54 : Poly := add (scale (1) (weightedSquare (w1) [false] [])) (add (scale (12) (weightedSquare (w2) [false] [])) (add (scale (5/3) (weightedSquare (w3) [false] [])) (scale (41/10) (weightedSquare (w4) [false] []))))
def residual54 : Poly := add (scale (14) (add (average 5 4) (scale (-1) (atom [false, false, true, false, true, false, true, false, true])))) (scale (-1) (rhs54))
theorem certificate54 : zeroCertificate residual54 := by decide +kernel
def g0_0 : Poly := add (atom [false, true, false, true]) (scale (-1) (atom [false, false, true, true]))
def g0_1 : Poly := add (atom [false, true, true, false]) (scale (-1) (atom [false, false, true, true]))
def g0_2 : Poly := add (atom [true, false, false, true]) (scale (-1) (atom [false, false, true, true]))
def g0_3 : Poly := add (atom [true, false, true, false]) (scale (-1) (atom [false, false, true, true]))
def g0_4 : Poly := add (atom [true, true, false, false]) (scale (-1) (atom [false, false, true, true]))
def gram0 : Poly := add (scale (102/5) (mul (mul (mul (adj g0_0) (atom [])) g0_0) (atom []))) (add (scale (-129/5) (mul (mul (mul (adj g0_0) (atom [])) g0_1) (atom []))) (add (scale (201/5) (mul (mul (mul (adj g0_0) (atom [])) g0_2) (atom []))) (add (scale (-136/5) (mul (mul (mul (adj g0_0) (atom [])) g0_3) (atom []))) (add (scale (-134/5) (mul (mul (mul (adj g0_0) (atom [])) g0_4) (atom []))) (add (scale (-129/5) (mul (mul (mul (adj g0_1) (atom [])) g0_0) (atom []))) (add (scale (293/5) (mul (mul (mul (adj g0_1) (atom [])) g0_1) (atom []))) (add (scale (-71) (mul (mul (mul (adj g0_1) (atom [])) g0_2) (atom []))) (add (scale (321/10) (mul (mul (mul (adj g0_1) (atom [])) g0_3) (atom []))) (add (scale (158/5) (mul (mul (mul (adj g0_1) (atom [])) g0_4) (atom []))) (add (scale (201/5) (mul (mul (mul (adj g0_2) (atom [])) g0_0) (atom []))) (add (scale (-71) (mul (mul (mul (adj g0_2) (atom [])) g0_1) (atom []))) (add (scale (634/5) (mul (mul (mul (adj g0_2) (atom [])) g0_2) (atom []))) (add (scale (-137/2) (mul (mul (mul (adj g0_2) (atom [])) g0_3) (atom []))) (add (scale (-135/2) (mul (mul (mul (adj g0_2) (atom [])) g0_4) (atom []))) (add (scale (-136/5) (mul (mul (mul (adj g0_3) (atom [])) g0_0) (atom []))) (add (scale (321/10) (mul (mul (mul (adj g0_3) (atom [])) g0_1) (atom []))) (add (scale (-137/2) (mul (mul (mul (adj g0_3) (atom [])) g0_2) (atom []))) (add (scale (228/5) (mul (mul (mul (adj g0_3) (atom [])) g0_3) (atom []))) (add (scale (224/5) (mul (mul (mul (adj g0_3) (atom [])) g0_4) (atom []))) (add (scale (-134/5) (mul (mul (mul (adj g0_4) (atom [])) g0_0) (atom []))) (add (scale (158/5) (mul (mul (mul (adj g0_4) (atom [])) g0_1) (atom []))) (add (scale (-135/2) (mul (mul (mul (adj g0_4) (atom [])) g0_2) (atom []))) (add (scale (224/5) (mul (mul (mul (adj g0_4) (atom [])) g0_3) (atom []))) (scale (222/5) (mul (mul (mul (adj g0_4) (atom [])) g0_4) (atom []))))))))))))))))))))))))))
def g1_0 : Poly := add (atom [true, false, true]) (scale (-1) (atom [false, true, true]))
def g1_1 : Poly := add (atom [true, true, false]) (scale (-1) (atom [false, true, true]))
def gram1 : Poly := add (scale (1/5) (mul (mul (mul (adj g1_0) (atom [false])) g1_0) (atom [false]))) (scale (129/5) (mul (mul (mul (adj g1_1) (atom [false])) g1_1) (atom [false])))
def g2_0 : Poly := add (atom [false, true, false]) (scale (-1) (atom [false, false, true]))
def g2_1 : Poly := add (atom [true, false, false]) (scale (-1) (atom [false, false, true]))
def gram2 : Poly := add (scale (1/5) (mul (mul (mul (adj g2_0) (atom [true])) g2_0) (atom [true]))) (scale (297/5) (mul (mul (mul (adj g2_1) (atom [true])) g2_1) (atom [true])))
def jordan : Poly := scale (1/2) (add (atom [false, true]) (atom [true, false]))
def jordan4 : Poly := mul (mul (mul jordan jordan) jordan) jordan
def rhs44 : Poly := add (gram0) (add (gram1) (gram2))
def residual44 : Poly := add (scale (560) (add (average 4 4) (scale (-1) (jordan4)))) (scale (-1) (rhs44))
theorem certificate44 : zeroCertificate residual44 := by decide +kernel

end RefinedBMV
