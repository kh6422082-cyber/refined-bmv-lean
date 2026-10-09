import RefinedBMV.CubicHolomorphic
import RefinedBMV.TwoLetterMatrix

namespace RefinedBMV
open scoped ComplexOrder MatrixOrder
set_option maxHeartbeats 500000

theorem reTrace_sub {d} (M N : Mat d) :
    reTrace (M-N) = reTrace M-reTrace N := by
  simp only [reTrace, Matrix.trace_sub, Complex.sub_re]

theorem commutator_second_moment_identity {d} (S T : Mat d)
    (hS : S.IsHermitian) (hT : T.IsHermitian) :
    reTrace ((S*T-T*S).conjTranspose*(S*T-T*S)) =
      2*(reTrace (S^2*T^2)-reTrace ((S*T)^2)) := by
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hS.eq, hT.eq]
  have he : (T*S-S*T)*(S*T-T*S) =
      (T*(S^2*T)+S*(T^2*S))-((T*S)^2+(S*T)^2) := by noncomm_ring
  rw [he, reTrace_sub, reTrace_add, reTrace_add, reTrace_cycle T (S^2*T),
    reTrace_cycle S (T^2*S)]
  have h1 : S^2*T*T = S^2*T^2 := by noncomm_ring
  have h2 : T^2*S*S = T^2*S^2 := by noncomm_ring
  rw [h1, h2, reTrace_cycle (T^2) (S^2), reTrace_mul_pow T S 2]
  ring

theorem cubic_center_deficit {d} (X Y : Mat d) (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    reTrace (X*Y)-reTrace ((CFC.sqrt X*CFC.sqrt Y)^2) =
      (1/2 : ℝ)*(∑ i, ∑ j, entrySquare
        ((CFC.sqrt X*CFC.sqrt Y-CFC.sqrt Y*CFC.sqrt X) j i)) := by
  have hS : (CFC.sqrt X).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg X)).isHermitian
  have hT : (CFC.sqrt Y).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg Y)).isHermitian
  have h := commutator_second_moment_identity (CFC.sqrt X) (CFC.sqrt Y) hS hT
  rw [reTrace_adj_mul, pow_two, CFC.sqrt_mul_sqrt_self X hX.nonneg,
    pow_two, CFC.sqrt_mul_sqrt_self Y hY.nonneg] at h
  linarith

theorem cubic_center_le_endpoint {d} (X Y : Mat d) (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    reTrace ((CFC.sqrt X*CFC.sqrt Y)^2) ≤ reTrace (X*Y) := by
  have he := cubic_center_deficit X Y hX hY
  have hsum : 0 ≤ ∑ i, ∑ j, entrySquare
      ((CFC.sqrt X*CFC.sqrt Y-CFC.sqrt Y*CFC.sqrt X) j i) :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => entrySquare_nonneg _))
  linarith

theorem cubic_center_pos {d} (hd : 0 < d) (X Y : Mat d) (hX : X.PosDef) (hY : Y.PosDef) :
    0 < reTrace ((CFC.sqrt X*CFC.sqrt Y)^2) := by
  let : NeZero d := ⟨by omega⟩
  let S := CFC.sqrt X
  let T := CFC.sqrt Y
  let R := CFC.sqrt T
  let K := R*S*R
  have hS : S.PosDef := Matrix.isStrictlyPositive_iff_posDef.mp
    (IsStrictlyPositive.sqrt X hX.isStrictlyPositive)
  have hT : T.PosDef := Matrix.isStrictlyPositive_iff_posDef.mp
    (IsStrictlyPositive.sqrt Y hY.isStrictlyPositive)
  have hR : R.PosDef := Matrix.isStrictlyPositive_iff_posDef.mp
    (IsStrictlyPositive.sqrt T hT.isStrictlyPositive)
  have hK : K.PosDef := by
    have h := (Matrix.IsUnit.posDef_star_left_conjugate_iff hR.isUnit).mpr hS
    simpa only [Matrix.star_eq_conjTranspose, hR.isHermitian.eq] using h
  have hK2 : (K^2).PosDef := (hK.posSemidef.pow 2).posDef_iff_isUnit.mpr (hK.isUnit.pow 2)
  have ht : 0 < reTrace (K^2) := (RCLike.pos_iff.mp hK2.trace_pos).1
  have hRR : R*R = T := CFC.sqrt_mul_sqrt_self T hT.posSemidef.nonneg
  have he : reTrace (K^2) = reTrace ((S*T)^2) := by
    have h := reTrace_mul_pow R (S*R) 2
    simpa only [K, mul_assoc, hRR] using h
  rw [he] at ht
  exact ht

theorem cubic_center_trace_real {d} (X Y : Mat d) :
    ((CFC.sqrt X*CFC.sqrt Y)^2).trace.im = 0 := by
  let S := CFC.sqrt X
  let T := CFC.sqrt Y
  let R := CFC.sqrt T
  have hS : S.IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg X)).isHermitian
  have hT : T.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg Y)
  have hR : R.IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg T)).isHermitian
  have hRR : R*R = T := CFC.sqrt_mul_sqrt_self T hT.nonneg
  have he : ((R*S*R)^2).trace = ((S*T)^2).trace := by
    have h := trace_mul_pow_complex R (S*R) 2
    simpa only [mul_assoc, hRR] using h
  rw [← he]
  exact hermitian_trace_im_zero _ ((sandwich_isHermitian R S hR hS).pow 2)

end RefinedBMV
