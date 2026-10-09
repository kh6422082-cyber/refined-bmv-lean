import RefinedBMV.ALTWeightedHolder

namespace RefinedBMV
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 700000

noncomputable def altTracePath {d} (A B P U : Mat d) (α : ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  (complexPower A ((α : ℂ)*z/2)*complexPower B ((α : ℂ)*z/2)*
    complexPower P ((N : ℂ)-(α : ℂ)*z)*star U).trace

theorem altTracePath_entire {d} (A B P U : Mat d) (α : ℝ) (N : ℕ) :
    Differentiable ℂ (altTracePath A B P U α N) := by
  let tr : Mat d →L[ℂ] ℂ := (Matrix.traceLinearMap (Fin d) ℂ ℂ).toContinuousLinearMap
  have hz : Differentiable ℂ (fun z : ℂ => (α : ℂ)*z/2) := by fun_prop
  have hpz : Differentiable ℂ (fun z : ℂ => (N : ℂ)-(α : ℂ)*z) := by fun_prop
  exact tr.differentiable.comp (((((complexPower_differentiable A).comp hz).mul
    ((complexPower_differentiable B).comp hz)).mul
    ((complexPower_differentiable P).comp hpz)).mul_const (star U))

theorem altTracePath_left {d} (A B P U : Mat d) (α : ℝ) (N : ℕ) (hP : P.PosDef)
    (hU : U ∈ unitary (Mat d)) (t : ℝ) :
    ‖altTracePath A B P U α N ((t : ℂ)*Complex.I)‖ ≤ reTrace (P^N) := by
  let v : ℂ := (t : ℂ)*Complex.I
  let ua := complexPower A ((α : ℂ)*v/2)
  let ub := complexPower B ((α : ℂ)*v/2)
  let up := complexPower P (-(α : ℂ)*v)
  have hua : ua ∈ unitary (Mat d) := complexPower_unitary_of_re_zero A _ (by simp [v])
  have hub : ub ∈ unitary (Mat d) := complexPower_unitary_of_re_zero B _ (by simp [v])
  have hup : up ∈ unitary (Mat d) := complexPower_unitary_of_re_zero P _ (by simp [v])
  have he : complexPower P ((N : ℂ)-(α : ℂ)*v) = P^N*up := by
    rw [← complexPower_nat P hP N,← complexPower_add]
    congr 1
    ring
  have htrace : altTracePath A B P U α N v = (P^N*(up*star U*ua*ub)).trace := by
    rw [altTracePath,he]
    change (ua*ub*(P^N*up)*star U).trace = _
    have hr : ua*ub*(P^N*up)*star U = (ua*ub)*(P^N*up*star U) := by simp only [mul_assoc]
    rw [hr,Matrix.trace_mul_comm]
    simp only [mul_assoc]
  rw [htrace]
  exact positive_unitary_trace_bound _ _ (hP.posSemidef.pow N)
    ((unitary (Mat d)).mul_mem ((unitary (Mat d)).mul_mem
      ((unitary (Mat d)).mul_mem hup (Unitary.star_mem hU)) hua) hub)

theorem altTracePath_right {d} (hdim : 0 < d) (A B P U : Mat d) (N q : ℕ)
    (hq : 0 < q) (hP : P.PosDef) (hU : U ∈ unitary (Mat d)) (t : ℝ) :
    ‖altTracePath A B P U ((N : ℝ)/(2*q)) N (1+(t : ℂ)*Complex.I)‖^(2*q) ≤
      traceMoment q (complexPower A ((((N : ℝ)/(4*q) : ℝ)) : ℂ)*
        complexPower B ((((N : ℝ)/(4*q) : ℝ)) : ℂ))*(reTrace (P^N))^(2*q-1) := by
  let α : ℝ := (N : ℝ)/(2*q)
  let v : ℂ := (t : ℂ)*Complex.I
  let ua := complexPower A ((α : ℂ)*v/2)
  let ub := complexPower B ((α : ℂ)*v/2)
  let up := complexPower P (-(α : ℂ)*v)
  let M := complexPower A (((α/2 : ℝ)) : ℂ)*complexPower B (((α/2 : ℝ)) : ℂ)
  have hua : ua ∈ unitary (Mat d) := complexPower_unitary_of_re_zero A _ (by simp [v])
  have hub : ub ∈ unitary (Mat d) := complexPower_unitary_of_re_zero B _ (by simp [v])
  have hup : up ∈ unitary (Mat d) := complexPower_unitary_of_re_zero P _ (by simp [v])
  have ha : complexPower A ((α : ℂ)*(1+v)/2) = ua*complexPower A (((α/2 : ℝ)) : ℂ) := by
    rw [← complexPower_add]
    congr 1
    push_cast
    ring
  have hb : complexPower B ((α : ℂ)*(1+v)/2) = complexPower B (((α/2 : ℝ)) : ℂ)*ub := by
    rw [← complexPower_add]
    congr 1
    push_cast
    ring
  have hp : complexPower P ((N : ℂ)-(α : ℂ)*(1+v)) =
      complexPower P (((N : ℝ)*(1-1/(2*q)) : ℝ) : ℂ)*up := by
    rw [← complexPower_add]
    congr 1
    dsimp [α]
    push_cast
    ring
  have ht : altTracePath A B P U α N (1+v) =
      ((ua*M*ub)*complexPower P (((N : ℝ)*(1-1/(2*q)) : ℝ) : ℂ)*(up*star U)).trace := by
    rw [altTracePath,ha,hb,hp]
    dsimp only [M]
    simp only [mul_assoc]
  have hM : IsUnit (ua*M*ub) := (complexPower_isUnit A _ |>.mul
    ((complexPower_isUnit A _).mul (complexPower_isUnit B _))).mul (complexPower_isUnit B _)
  have h := alt_weighted_holder hdim (ua*M*ub) P (up*star U) N q hq hM hP
    ((unitary (Mat d)).mul_mem hup (Unitary.star_mem hU))
  rw [traceMoment_right_unitary _ _ _ hub,traceMoment_left_unitary _ _ _ hua] at h
  have he : α/2 = (N : ℝ)/(4*q) := by dsimp [α]; ring
  rw [ht]
  simpa only [M,he] using h

theorem altTracePath_polar_point {d} (A B P U : Mat d) (α θ : ℝ) (N : ℕ)
    (hN : 0 < N) (hαθ : α*θ=1) (hP : P.PosDef) (hU : U ∈ unitary (Mat d))
    (hM : complexPower A (1/2)*complexPower B (1/2) = U*P) :
    ‖altTracePath A B P U α N (θ : ℂ)‖ = reTrace (P^N) := by
  have hc : (α : ℂ)*(θ : ℂ)=1 := by exact_mod_cast hαθ
  have hn : (N : ℂ)-1 = ((N-1 : ℕ) : ℂ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ N)]
    norm_num
  rw [altTracePath,hc,hn,complexPower_nat P hP (N-1),hM]
  have he : U*P*P^(N-1)*star U = U*P^N*star U := by
    rw [mul_assoc U P,← pow_succ',Nat.sub_add_cancel hN]
  rw [he,Matrix.trace_mul_comm (U*P^N) (star U),← mul_assoc,
    Unitary.star_mul_self_of_mem hU,one_mul]
  have hr : (P^N).trace = (reTrace (P^N) : ℂ) := by
    apply Complex.ext
    · rfl
    · simp only [Complex.ofReal_im]
      exact hermitian_trace_im_zero _ (hP.isHermitian.pow N)
  have h0 : 0 ≤ reTrace (P^N) := (RCLike.nonneg_iff.mp (hP.posSemidef.pow N).trace_nonneg).1
  rw [hr,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg h0]

theorem altTracePath_bounded {d} (A B P U : Mat d) (α : ℝ) (N : ℕ) (hα : 0 ≤ α) :
    ∃ K : ℝ, ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → ‖altTracePath A B P U α N z‖ ≤ K := by
  obtain ⟨CA,hCA,bA⟩ := complexPower_bounded_strip A 0 (α/2)
  obtain ⟨CB,hCB,bB⟩ := complexPower_bounded_strip B 0 (α/2)
  obtain ⟨CP,hCP,bP⟩ := complexPower_bounded_strip P ((N : ℝ)-α) N
  let tr : Mat d →L[ℂ] ℂ := (Matrix.traceLinearMap (Fin d) ℂ ℂ).toContinuousLinearMap
  refine ⟨‖tr‖*(CA*CB*CP*‖star U‖),?_⟩
  intro z hlo hhi
  have hrA : ((α : ℂ)*z/2).re = α*z.re/2 := by simp
  have hrP : ((N : ℂ)-(α : ℂ)*z).re = (N : ℝ)-α*z.re := by simp
  have hAr := bA ((α : ℂ)*z/2) (by rw [hrA]; positivity) (by rw [hrA]; nlinarith)
  have hBr := bB ((α : ℂ)*z/2) (by rw [hrA]; positivity) (by rw [hrA]; nlinarith)
  have hPr := bP ((N : ℂ)-(α : ℂ)*z) (by rw [hrP]; nlinarith) (by rw [hrP]; nlinarith)
  have ht : ‖complexPower A ((α : ℂ)*z/2)*complexPower B ((α : ℂ)*z/2)*
      complexPower P ((N : ℂ)-(α : ℂ)*z)*star U‖ ≤ CA*CB*CP*‖star U‖ := by
    apply (norm_mul_le _ _).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply (norm_mul_le _ _).trans
    apply mul_le_mul ((norm_mul_le _ _).trans
      (mul_le_mul hAr hBr (norm_nonneg _) hCA)) hPr (norm_nonneg _) (mul_nonneg hCA hCB)
  exact (tr.le_opNorm _).trans (mul_le_mul_of_nonneg_left ht (norm_nonneg tr))

end RefinedBMV
