import Quantum.TraceInequality.Core
import Quantum.TraceInequality.CompressionInequality.BlockMatrix
import Quantum.TraceInequality.Basic
/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.CompressionInequality.DefectOperators

/-!
# Julia unitary blocks for contractions

This file proves the unitary block identities used in the compression
inequality part of the Hansen–Pedersen characterization.  The main block is
the Julia operator built from a contraction and its left and right defect
operators.

## Main results

* `julia_block_mem_unitary`: the Julia block of a contraction is unitary.
* `signFlip_block_mem_unitary`: the diagonal sign-flip block is unitary.

## References

* Hiai--Yanagi, *Hilbert spaces and linear operators*,
  Ohmsha, 2021, Section 5.1, Theorem 5.1.7.
-/

namespace HansenPedersen

universe u v

open CFC MeasureTheory
open scoped Topology
open Filter

section NormalCFC517

namespace ConvexityCharacterization

open scoped ComplexOrder

section JuliaUnitary

/-- The Julia block matrix of a contraction `C`, formed from the left and right
defect operators, is unitary on the doubled Hilbert space. -/
theorem julia_block_mem_unitary {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)]
    {C : L K} (hC : ‖C‖ ≤ 1) :
    blockCLM C (-(defectLeft C)) (defectRight C) (star C) ∈
      unitary (L (WithLp 2 (K × K))) := by
  let U : L (WithLp 2 (K × K)) :=
    blockCLM C (-(defectLeft C)) (defectRight C) (star C)
  have hDstar : star (defectRight C) = defectRight C :=
    (defectRight_selfAdjoint (K := K) C).star_eq
  have hEstar : star (defectLeft C) = defectLeft C :=
    (defectLeft_selfAdjoint (K := K) C).star_eq
  rw [Unitary.mem_iff]
  constructor
  · change star U * U = (1 : L (WithLp 2 (K × K)))
    dsimp [U]
    rw [blockCLM_star, blockCLM_mul]
    have h11 : star C * C + star (defectRight C) * defectRight C = (1 : L K) := by
      calc
        star C * C + star (defectRight C) * defectRight C
            = star C * C + defectRight C * defectRight C := by
                simp [hDstar]
        _ = star C * C + ((1 : L K) - star C * C) := by
              rw [defectRight_sq (K := K) hC]
        _ = (1 : L K) := by
              simp [sub_eq_add_neg, add_left_comm, add_comm]
    have h12 : star C * (-(defectLeft C)) + star (defectRight C) * star C = (0 : L K) := by
      calc
        star C * (-(defectLeft C)) + star (defectRight C) * star C
            = -(star C * defectLeft C) + defectRight C * star C := by
                simp [hDstar]
        _ = 0 := by rw [star_defect_intertwine (K := K) hC]; simp
    have h21 : star (-(defectLeft C)) * C + star (star C) * defectRight C = (0 : L K) := by
      calc
        star (-(defectLeft C)) * C + star (star C) * defectRight C
            = -(defectLeft C * C) + C * defectRight C := by
                simp [hEstar]
        _ = 0 := by rw [defect_intertwine (K := K) hC]; simp
    have h22 :
        star (-(defectLeft C)) * (-(defectLeft C)) + star (star C) * star C = (1 : L K) := by
      calc
        star (-(defectLeft C)) * (-(defectLeft C)) + star (star C) * star C
            = defectLeft C * defectLeft C + C * star C := by
                simp [hEstar]
        _ = ((1 : L K) - C * star C) + C * star C := by
              rw [defectLeft_sq (K := K) hC]
        _ = (1 : L K) := by
              simp [sub_eq_add_neg, add_left_comm, add_comm]
    rw [h11, h12, h21, h22, blockCLM_one]
  · change U * star U = (1 : L (WithLp 2 (K × K)))
    dsimp [U]
    rw [blockCLM_star, blockCLM_mul]
    have h11 : C * star C + -(defectLeft C) * star (-(defectLeft C)) = (1 : L K) := by
      calc
        C * star C + -(defectLeft C) * star (-(defectLeft C))
            = C * star C + defectLeft C * defectLeft C := by
                simp [hEstar]
        _ = C * star C + ((1 : L K) - C * star C) := by
              rw [defectLeft_sq (K := K) hC]
        _ = (1 : L K) := by
              simp [sub_eq_add_neg, add_left_comm, add_comm]
    have h12 : C * star (defectRight C) + -(defectLeft C) * star (star C) = (0 : L K) := by
      calc
        C * star (defectRight C) + -(defectLeft C) * star (star C)
            = C * defectRight C - defectLeft C * C := by
                simp [hDstar, sub_eq_add_neg]
        _ = 0 := by rw [defect_intertwine (K := K) hC]; simp
    have h21 : defectRight C * star C + star C * star (-(defectLeft C)) = (0 : L K) := by
      calc
        defectRight C * star C + star C * star (-(defectLeft C))
            = defectRight C * star C - star C * defectLeft C := by
                simp [hEstar, sub_eq_add_neg]
        _ = 0 := by rw [star_defect_intertwine (K := K) hC]; simp
    have h22 :
        defectRight C * star (defectRight C) + star C * star (star C) = (1 : L K) := by
      calc
        defectRight C * star (defectRight C) + star C * star (star C)
            = defectRight C * defectRight C + star C * C := by
                simp [hDstar]
        _ = ((1 : L K) - star C * C) + star C * C := by
              rw [defectRight_sq (K := K) hC]
        _ = (1 : L K) := by
              simp [sub_eq_add_neg, add_left_comm, add_comm]
    rw [h11, h12, h21, h22, blockCLM_one]

/-- The diagonal block `diag(1, -1)` is unitary on the doubled Hilbert space;
it is used as a sign-changing auxiliary block. -/
theorem signFlip_block_mem_unitary {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)] :
    blockCLM (1 : L K) 0 0 (- (1 : L K)) ∈ unitary (L (WithLp 2 (K × K))) := by
  rw [Unitary.mem_iff]
  constructor
  · rw [blockCLM_star, blockCLM_mul]
    ext x
    apply WithLp.ofLp_injective
    ext
    · simp
    · simp
  · rw [blockCLM_star, blockCLM_mul]
    ext x
    apply WithLp.ofLp_injective
    ext
    · simp
    · simp

end JuliaUnitary

end ConvexityCharacterization

end NormalCFC517

end HansenPedersen
