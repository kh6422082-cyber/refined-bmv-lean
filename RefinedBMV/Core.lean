import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! Exact finite noncommutative polynomials and their complex-matrix interpretation.
Only real traces are identified under reversal. No individual word is asserted real.
-/
namespace RefinedBMV
open scoped ComplexOrder

abbrev Word := List Bool
abbrev Poly := List (ℚ × Word)
abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℂ

def evalWord {d : ℕ} (A B : Mat d) : Word → Mat d
  | [] => 1
  | b :: w => (if b then B else A) * evalWord A B w

def reTrace {d : ℕ} (M : Mat d) : ℝ := M.trace.re

def trWord {d : ℕ} (A B : Mat d) (w : Word) : ℝ := reTrace (evalWord A B w)

noncomputable def evalPoly {d : ℕ} (A B : Mat d) (p : Poly) : Mat d :=
  (p.map fun t => (t.1 : ℝ) • evalWord A B t.2).sum

def tracePoly {d : ℕ} (A B : Mat d) (p : Poly) : ℝ :=
  (p.map fun t => (t.1 : ℝ) * trWord A B t.2).sum

def atom (w : Word) : Poly := [(1, w)]
def scale (c : ℚ) (p : Poly) : Poly := p.map fun t => (c * t.1, t.2)
def add (p q : Poly) : Poly := p ++ q
def mul (p q : Poly) : Poly :=
  p.flatMap fun s => q.map fun t => (s.1 * t.1, s.2 ++ t.2)
def adj (p : Poly) : Poly := p.map fun t => (t.1, t.2.reverse)
def weightedSquare (p : Poly) (l r : Word) : Poly :=
  mul (mul (mul (adj p) (atom l)) p) (atom r)

@[simp] theorem reTrace_add {d} (M N : Mat d) :
    reTrace (M + N) = reTrace M + reTrace N := by simp [reTrace]
@[simp] theorem reTrace_smul {d} (c : ℝ) (M : Mat d) :
    reTrace (c • M) = c * reTrace M := by simp [reTrace, Complex.real_smul]
@[simp] theorem reTrace_zero {d} : reTrace (0 : Mat d) = 0 := by simp [reTrace]
@[simp] theorem reTrace_adj {d} (M : Mat d) :
    reTrace M.conjTranspose = reTrace M := by simp [reTrace]
theorem reTrace_cycle {d} (M N : Mat d) : reTrace (M * N) = reTrace (N * M) :=
  congrArg Complex.re (Matrix.trace_mul_comm M N)

theorem evalWord_append {d} (A B : Mat d) (u v : Word) :
    evalWord A B (u ++ v) = evalWord A B u * evalWord A B v := by
  induction u with
  | nil => simp [evalWord]
  | cons b u ih => simp [evalWord, ih, mul_assoc]

theorem evalWord_reverse {d} (A B : Mat d) (hA : A.IsHermitian)
    (hB : B.IsHermitian) (w : Word) :
    evalWord A B w.reverse = (evalWord A B w).conjTranspose := by
  induction w with
  | nil => simp [evalWord]
  | cons b w ih =>
    simp only [List.reverse_cons, evalWord_append, ih, evalWord,
      Matrix.conjTranspose_mul]
    cases b <;> simp [hA.eq, hB.eq]

theorem trWord_cycle {d} (A B : Mat d) (u v : Word) :
    trWord A B (u ++ v) = trWord A B (v ++ u) := by
  simp only [trWord, evalWord_append]
  exact reTrace_cycle _ _

theorem trWord_reverse {d} (A B : Mat d) (hA : A.IsHermitian)
    (hB : B.IsHermitian) (w : Word) :
    trWord A B w.reverse = trWord A B w := by
  simp [trWord, evalWord_reverse A B hA hB]

theorem tracePoly_eq {d} (A B : Mat d) (p : Poly) :
    tracePoly A B p = reTrace (evalPoly A B p) := by
  induction p with
  | nil => simp [tracePoly, evalPoly]
  | cons t p ih =>
    change (t.1 : ℝ) * trWord A B t.2 + tracePoly A B p =
      reTrace ((t.1 : ℝ) • evalWord A B t.2 + evalPoly A B p)
    rw [reTrace_add, reTrace_smul, ih]
    rfl

@[simp] theorem evalPoly_atom {d} (A B : Mat d) (w : Word) :
    evalPoly A B (atom w) = evalWord A B w := by simp [evalPoly, atom]
@[simp] theorem evalPoly_add {d} (A B : Mat d) (p q : Poly) :
    evalPoly A B (add p q) = evalPoly A B p + evalPoly A B q := by
  simp [evalPoly, add]
@[simp] theorem evalPoly_scale {d} (A B : Mat d) (c : ℚ) (p : Poly) :
    evalPoly A B (scale c p) = (c : ℝ) • evalPoly A B p := by
  induction p with
  | nil => simp [evalPoly, scale]
  | cons t p ih =>
    change ((c * t.1 : ℚ) : ℝ) • evalWord A B t.2 + evalPoly A B (scale c p) =
      (c : ℝ) • ((t.1 : ℝ) • evalWord A B t.2 + evalPoly A B p)
    rw [ih]
    simp [smul_add, mul_smul]
@[simp] theorem evalPoly_mul {d} (A B : Mat d) (p q : Poly) :
    evalPoly A B (mul p q) = evalPoly A B p * evalPoly A B q := by
  induction p with
  | nil => simp [evalPoly, mul]
  | cons s p ih =>
    change evalPoly A B (add (q.map fun t => (s.1 * t.1, s.2 ++ t.2)) (mul p q)) = _
    rw [evalPoly_add, ih]
    have ht : evalPoly A B (q.map fun t => (s.1 * t.1, s.2 ++ t.2)) =
        ((s.1 : ℝ) • evalWord A B s.2) * evalPoly A B q := by
      clear ih
      induction q with
      | nil => simp [evalPoly]
      | cons t q ihq =>
        change ((s.1 * t.1 : ℚ) : ℝ) • evalWord A B (s.2 ++ t.2) +
          evalPoly A B (q.map fun t => (s.1 * t.1, s.2 ++ t.2)) =
          ((s.1 : ℝ) • evalWord A B s.2) *
            ((t.1 : ℝ) • evalWord A B t.2 + evalPoly A B q)
        rw [ihq, evalWord_append]
        simp [mul_add, smul_smul, mul_comm]
    change evalPoly A B (q.map fun t => (s.1 * t.1, s.2 ++ t.2)) + _ = _
    rw [ht]
    change _ = (((s.1 : ℝ) • evalWord A B s.2) + evalPoly A B p) * evalPoly A B q
    rw [add_mul]
@[simp] theorem evalPoly_adj {d} (A B : Mat d) (hA : A.IsHermitian)
    (hB : B.IsHermitian) (p : Poly) :
    evalPoly A B (adj p) = (evalPoly A B p).conjTranspose := by
  induction p with
  | nil => simp [evalPoly, adj]
  | cons t p ih =>
    change (t.1 : ℝ) • evalWord A B t.2.reverse + evalPoly A B (adj p) =
      ((t.1 : ℝ) • evalWord A B t.2 + evalPoly A B p).conjTranspose
    rw [ih, evalWord_reverse A B hA hB]
    simp [Matrix.conjTranspose_smul]

theorem evalPoly_weightedSquare {d} (A B : Mat d) (hA : A.IsHermitian)
    (hB : B.IsHermitian) (p : Poly) (l r : Word) :
    evalPoly A B (weightedSquare p l r) =
      (evalPoly A B p).conjTranspose * evalWord A B l *
        evalPoly A B p * evalWord A B r := by
  simp [weightedSquare, evalPoly_adj A B hA hB]

/- The normalization algorithm only uses cyclic rotations and reversal. -/
def wordCode (w : Word) : ℕ := w.foldl (fun n b => 2 * n + if b then 1 else 0) 0
def choose (u v : Word) : Word := if wordCode u ≤ wordCode v then u else v
def rotations (w : Word) : List Word :=
  (List.range (w.length + 1)).map fun k => w.drop k ++ w.take k
def canonical (w : Word) : Word :=
  (rotations w ++ rotations w.reverse).foldl choose w

theorem trWord_rotation {d} (A B : Mat d) (w : Word) (k : ℕ) :
    trWord A B (w.drop k ++ w.take k) = trWord A B w := by
  rw [trWord_cycle, List.take_append_drop]

theorem trWord_canonical {d} (A B : Mat d) (hA : A.IsHermitian)
    (hB : B.IsHermitian) (w : Word) :
    trWord A B (canonical w) = trWord A B w := by
  have hc : ∀ v ∈ rotations w ++ rotations w.reverse,
      trWord A B v = trWord A B w := by
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · obtain ⟨k, _, rfl⟩ := List.mem_map.mp hv
      exact trWord_rotation A B w k
    · obtain ⟨k, _, rfl⟩ := List.mem_map.mp hv
      rw [trWord_rotation, trWord_reverse A B hA hB]
  have hf : ∀ (vs : List Word) (v : Word),
      trWord A B v = trWord A B w →
      (∀ u ∈ vs, trWord A B u = trWord A B w) →
      trWord A B (vs.foldl choose v) = trWord A B w := by
    intro vs
    induction vs with
    | nil => intro v hv _; exact hv
    | cons u vs ih =>
      intro v hv hs
      apply ih
      · unfold choose
        split_ifs <;> first | exact hv | exact hs u (by simp)
      · intro z hz; exact hs z (by simp [hz])
  exact hf _ w rfl hc

def insert (c : ℚ) (w : Word) : Poly → Poly
  | [] => [(c, w)]
  | (a, v) :: p => if w = v then (c + a, v) :: p else (a, v) :: insert c w p
def collect : Poly → Poly
  | [] => []
  | (c, w) :: p => insert c (canonical w) (collect p)

theorem tracePoly_insert {d} (A B : Mat d) (c : ℚ) (w : Word) (p : Poly) :
    tracePoly A B (insert c w p) = (c : ℝ) * trWord A B w + tracePoly A B p := by
  induction p with
  | nil => simp [insert, tracePoly]
  | cons t p ih =>
    rcases t with ⟨a,v⟩
    simp only [insert]
    split_ifs with h
    · subst v; simp [tracePoly, add_mul]; ring
    · change (a : ℝ) * trWord A B v + tracePoly A B (insert c w p) =
        (c : ℝ) * trWord A B w + ((a : ℝ) * trWord A B v + tracePoly A B p)
      rw [ih]; ring

theorem tracePoly_collect {d} (A B : Mat d) (hA : A.IsHermitian)
    (hB : B.IsHermitian) (p : Poly) :
    tracePoly A B (collect p) = tracePoly A B p := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    rcases t with ⟨c,w⟩
    rw [collect, tracePoly_insert, ih, trWord_canonical A B hA hB]
    rfl

def zeroCertificate (p : Poly) : Prop := ∀ t ∈ collect p, t.1 = 0
instance (p : Poly) : Decidable (zeroCertificate p) := by
  unfold zeroCertificate; infer_instance

theorem tracePoly_zero_of_certificate {d} (A B : Mat d) (hA : A.IsHermitian)
    (hB : B.IsHermitian) (p : Poly) (hp : zeroCertificate p) :
    reTrace (evalPoly A B p) = 0 := by
  rw [← tracePoly_eq, ← tracePoly_collect A B hA hB]
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
  simp [hp t ht]

theorem matrix_weightedSquare_nonneg {d} (A M : Mat d) (hA : A.PosSemidef) :
    0 ≤ reTrace (M.conjTranspose * A * M) :=
  (Complex.nonneg_iff.mp (hA.conjTranspose_mul_mul_same M).trace_nonneg).1

end RefinedBMV
