import RefinedBMV.CubicQuantitative

namespace RefinedBMV
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator NNReal
set_option maxHeartbeats 500000

/-- The r=3,q=1 ALT instance follows from the cubic comparison and its center bound. -/
theorem third_moment_le {d} (hdim : 0 < d) (X Y : Mat d) (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    reTrace ((X*Y)^3) ≤ reTrace (X^3*Y^3) :=
  (cubic_alt_psd hdim X Y hX hY).trans
    (cubic_center_le_endpoint (X^3) (Y^3) (hX.pow 3) (hY.pow 3))

theorem sandwich_third_le {d} (hdim : 0 < d) (J C : Mat d) (hJ : J.PosSemidef) (hC : C.PosSemidef) :
    reTrace ((CFC.sqrt C*J*CFC.sqrt C)^3) ≤ reTrace (J^3*C^3) := by
  have he : reTrace ((CFC.sqrt C*J*CFC.sqrt C)^3) = reTrace ((J*C)^3) := by
    unfold reTrace
    rw [← product_nat_trace_sandwich C J hC 3,trace_mul_pow_complex C J 3]
  rw [he]
  exact third_moment_le hdim J C hJ hC

theorem weighted_third_sandwich_trace {d} (A B : Mat d) (hA : A.PosSemidef) :
    reTrace ((CFC.sqrt A*B*CFC.sqrt A)^3*A) = reTrace (A^2*B*A*B*A*B) := by
  let S := CFC.sqrt A
  have hSS : S*S = A := CFC.sqrt_mul_sqrt_self A hA.nonneg
  have he : (S*B*S)^3 = S*(B*(S*S)*B*(S*S)*B)*S := by noncomm_ring
  change reTrace ((S*B*S)^3*A) = _
  rw [he,hSS]
  have hr : S*(B*A*B*A*B)*S*A = S*((B*A*B*A*B)*S*A) := by noncomm_ring
  rw [hr,reTrace_cycle S]
  have hSAS : S*A*S = A^2 := by rw [← hSS]; noncomm_ring
  have he2 : ((B*A*B*A*B)*S*A)*S = (B*A*B*A*B)*(S*A*S) := by noncomm_ring
  rw [he2,hSAS,reTrace_cycle]
  simp only [mul_assoc]

theorem positivePower_one_third_cube {d} (A : Mat d) (hA : A.PosSemidef) :
    (positivePower A (1/3))^3 = A := by
  have htwo : positivePower A (1/3)*positivePower A (1/3) = positivePower A (2/3) := by
    rw [positivePower_add A _ _ (by norm_num) (by norm_num)]
    norm_num
  rw [pow_succ,pow_two,htwo,positivePower_add A _ _ (by norm_num) (by norm_num)]
  norm_num
  have hn := positivePower_nat A hA 1 (by norm_num)
  norm_num at hn
  exact hn

/-- The formerly missing W43>=T43 arrow, including singular inputs. -/
theorem weighted_third_ge_target {d} (hdim : 0 < d) (A B : Mat d)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    paperT 4 3 A B ≤ reTrace (A^2*B*A*B*A*B) := by
  let S := CFC.sqrt A
  let J := S*B*S
  let C := positivePower A (1/3)
  have hS : S.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian
  have hJ : J.PosSemidef := by simpa only [hS.eq] using hB.mul_mul_conjTranspose_same S
  have hC : C.PosSemidef := positivePower_nonneg A (1/3)
  have h := sandwich_third_le hdim J C hJ hC
  have hLeft : CFC.sqrt C*J*CFC.sqrt C = positivePower A (2/3)*B*positivePower A (2/3) := by
    have hR : CFC.sqrt C = positivePower A (1/6) := by
      dsimp [C]
      rw [sqrt_positivePower]
      norm_num
    have hRS : positivePower A (1/6)*S = positivePower A (2/3) := by
      dsimp [S]
      rw [sqrt_eq_positivePower,positivePower_add A _ _ (by norm_num) (by norm_num)]
      norm_num
    have hSR : S*positivePower A (1/6) = positivePower A (2/3) := by
      dsimp [S]
      rw [sqrt_eq_positivePower,positivePower_add A _ _ (by norm_num) (by norm_num)]
      norm_num
    rw [hR]
    change positivePower A (1/6)*(S*B*S)*positivePower A (1/6) = _
    have he : positivePower A (1/6)*(S*B*S)*positivePower A (1/6) =
        (positivePower A (1/6)*S)*B*(S*positivePower A (1/6)) := by noncomm_ring
    rw [he,hRS,hSR]
  have hRight : reTrace (J^3*C^3) = reTrace (A^2*B*A*B*A*B) := by
    change reTrace (J^3*(positivePower A (1/3))^3) = _
    rw [positivePower_one_third_cube A hA]
    exact weighted_third_sandwich_trace A B hA
  rw [hLeft,hRight] at h
  have ht : paperT 4 3 A B = reTrace ((positivePower A (2/3)*B*positivePower A (2/3))^3) := by
    norm_num [paperT]
  rw [ht]
  exact h

/-- The complete PSD strong statement of Proposition 4.1, (4.1). -/
theorem paper_proposition_4_1_psd {d} (hdim : 0 < d) (A B : Mat d)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    reTrace (A^2*B*A*B*A*B) ≤ p 4 3 A B ∧
    paperT 4 3 A B ≤ reTrace (A^2*B*A*B*A*B) :=
  ⟨p43_ge_W A B hA.isHermitian hB,weighted_third_ge_target hdim A B hA hB⟩

end RefinedBMV
