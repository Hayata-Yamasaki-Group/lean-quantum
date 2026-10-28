/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.Ambient.MatrixInstances
import Quantum.TraceInequality.HiaiPetz.TraceConvexity.LiebConcavity

/-!
# Three-variable convexity: base development

Infrastructure for the three-variable convexity of Hiai–Petz Theorem 6.4, built on two-block
diagonal embeddings `twoBlockDiag` and the associated power-trace estimates.

## Main results

* `matrixPower_twoBlockDiag_posDef`: positive-definiteness of matrix powers of a two-block
  diagonal matrix.
* `powerTrace_tendsto_exponents_posDef`, `powerTrace_right_comp_posDef`,
  `powerTrace_le_of_right_power_le_posDef`: continuity in the exponents and the monotone
  comparison estimates for the power trace on positive-definite inputs.
* `inverseTracePower_jointlyConvex`: joint convexity of `inverseTracePower p`, represented
  internally as `powerTrace (-p) (p - 1)`.

## References

* Hiai, Theorem 6.4.
-/

namespace HiaiPetz

namespace TraceConvexity

open Matrix
open scoped ComplexOrder MatrixOrder Topology
open scoped Matrix.Norms.Frobenius
open scoped HiaiPetz.AmbientInstances

noncomputable section MatrixScopedInstances

/-- Local API: auxiliary algebraic fact; used in Hiai, proof of Theorem 6.4. -/
private theorem twoBlockDiag_zero {n : ℕ} :
    twoBlockDiag (0 : Mₙ n) (0 : Mₙ n) = (0 : Mₙ (2 * n)) := by
  apply (reindexToBlockEquiv n).injective
  simp [twoBlockDiag, reindexToBlockEquiv]

/-- Source: Hiai, proof of Theorem 6.4. -/
private theorem twoBlockDiag_add {n : ℕ} (A₁ A₂ B₁ B₂ : Mₙ n) :
    twoBlockDiag (A₁ + B₁) (A₂ + B₂) =
      twoBlockDiag A₁ A₂ + twoBlockDiag B₁ B₂ := by
  apply (reindexToBlockEquiv n).injective
  calc
    reindexToBlockMatrix n (twoBlockDiag (A₁ + B₁) (A₂ + B₂))
        = Matrix.fromBlocks (A₁ + B₁) 0 0 (A₂ + B₂) := by simp
    _ = Matrix.fromBlocks A₁ 0 0 A₂ + Matrix.fromBlocks B₁ 0 0 B₂ := by
          ext i j
          cases i with
          | inl i₁ =>
              cases j <;> simp [Matrix.fromBlocks]
          | inr i₂ =>
              cases j <;> simp [Matrix.fromBlocks]
    _ = reindexToBlockMatrix n (twoBlockDiag A₁ A₂ + twoBlockDiag B₁ B₂) := by
          simp

/-- Source: Hiai, proof of Theorem 6.4. -/
private theorem twoBlockDiag_smul {n : ℕ} (a : ℂ) (A B : Mₙ n) :
    twoBlockDiag (a • A) (a • B) = a • twoBlockDiag A B := by
  apply (reindexToBlockEquiv n).injective
  calc
    reindexToBlockMatrix n (twoBlockDiag (a • A) (a • B))
        = Matrix.fromBlocks (a • A) 0 0 (a • B) := by simp
    _ = a • Matrix.fromBlocks A 0 0 B := by
          ext i j
          cases i with
          | inl i₁ =>
              cases j <;> simp [Matrix.fromBlocks]
          | inr i₂ =>
              cases j <;> simp [Matrix.fromBlocks]
    _ = reindexToBlockMatrix n (a • twoBlockDiag A B) := by
          simp

/-- Source: Hiai, proof of Theorem 6.4. -/
private theorem twoBlockDiag_one {n : ℕ} :
    twoBlockDiag (1 : Mₙ n) (1 : Mₙ n) = (1 : Mₙ (2 * n)) := by
  apply (reindexToBlockEquiv n).injective
  let e : Fin (2 * n) ≃ Fin n ⊕ Fin n :=
    (finCongr (by simp [two_mul])).trans finSumFinEquiv.symm
  calc
    reindexToBlockMatrix n (twoBlockDiag (1 : Mₙ n) (1 : Mₙ n))
        = Matrix.fromBlocks (1 : Mₙ n) 0 0 (1 : Mₙ n) := by simp
    _ = 1 := Matrix.fromBlocks_one
    _ = reindexToBlockMatrix n (1 : Mₙ (2 * n)) := by
          simp [reindexToBlockMatrix, reindexToBlockEquiv]

/-- Source: Hiai, proof of Theorem 6.4. -/
private theorem twoBlockDiag_algebraMap {n : ℕ} (z : ℂ) :
    twoBlockDiag ((algebraMap ℂ (Mₙ n)) z) ((algebraMap ℂ (Mₙ n)) z) =
      (algebraMap ℂ (Mₙ (2 * n))) z := by
  apply (reindexToBlockEquiv n).injective
  let e : Fin (2 * n) ≃ Fin n ⊕ Fin n :=
    (finCongr (by simp [two_mul])).trans finSumFinEquiv.symm
  have hfrom :
      Matrix.fromBlocks ((algebraMap ℂ (Mₙ n)) z) 0 0
          ((algebraMap ℂ (Mₙ n)) z) =
        (algebraMap ℂ (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)) z := by
    rw [Matrix.algebraMap_eq_diagonal, Matrix.algebraMap_eq_diagonal]
    ext i j
    cases i with
    | inl i₁ =>
        cases j with
        | inl j₁ =>
            simp [Matrix.fromBlocks, Matrix.diagonal]
        | inr j₂ =>
            simp [Matrix.fromBlocks, Matrix.diagonal]
    | inr i₂ =>
        cases j with
        | inl j₁ =>
            simp [Matrix.fromBlocks, Matrix.diagonal]
        | inr j₂ =>
            simp [Matrix.fromBlocks, Matrix.diagonal]
  calc
    reindexToBlockMatrix n
        (twoBlockDiag ((algebraMap ℂ (Mₙ n)) z) ((algebraMap ℂ (Mₙ n)) z))
        = Matrix.fromBlocks ((algebraMap ℂ (Mₙ n)) z) 0 0
            ((algebraMap ℂ (Mₙ n)) z) := by simp
    _ = (algebraMap ℂ (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)) z := hfrom
    _ = reindexToBlockMatrix n ((algebraMap ℂ (Mₙ (2 * n))) z) := by
          change (algebraMap ℂ (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)) z =
            (Matrix.reindexAlgEquiv ℂ ℂ e) ((algebraMap ℂ (Mₙ (2 * n))) z)
          exact ((Matrix.reindexAlgEquiv ℂ ℂ e).commutes z).symm

/-- Source: Hiai, proof of Theorem 6.4. -/
private theorem twoBlockDiag_pow {n : ℕ} (k : ℕ) (A B : Mₙ n) :
    (twoBlockDiag A B) ^ k = twoBlockDiag (A ^ k) (B ^ k) := by
  induction k with
  | zero =>
      simpa using (twoBlockDiag_one (n := n)).symm
  | succ k ih =>
      rw [pow_succ, ih, pow_succ, pow_succ]
      simpa using (twoBlockDiag_mul (A ^ k) (B ^ k) A B)

/-- Source: Hiai, proof of Theorem 6.4. -/
private theorem polynomial_aeval_twoBlockDiag {n : ℕ} (q : Polynomial ℂ)
    (A B : Mₙ n) :
    Polynomial.aeval (twoBlockDiag A B) q =
      twoBlockDiag (Polynomial.aeval A q) (Polynomial.aeval B q) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [Polynomial.aeval_add, Polynomial.aeval_add, Polynomial.aeval_add, hp, hq]
      exact (twoBlockDiag_add _ _ _ _).symm
  | monomial k a =>
      rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, Polynomial.aeval_monomial]
      rw [twoBlockDiag_pow]
      calc
        (algebraMap ℂ (Mₙ (2 * n))) a * twoBlockDiag (A ^ k) (B ^ k)
            = twoBlockDiag ((algebraMap ℂ (Mₙ n)) a) ((algebraMap ℂ (Mₙ n)) a) *
                twoBlockDiag (A ^ k) (B ^ k) := by
              rw [twoBlockDiag_algebraMap]
        _ = twoBlockDiag ((algebraMap ℂ (Mₙ n)) a * A ^ k)
              ((algebraMap ℂ (Mₙ n)) a * B ^ k) := by
              rw [twoBlockDiag_mul]

/-- Source: Hiai, proof of Theorem 6.4. -/
theorem matrixPower_twoBlockDiag_posDef {n : ℕ} {r : ℝ}
    {A B : Mₙ n} (hA : Matrix.PosDef A) (hB : Matrix.PosDef B) :
    matrixPower r (twoBlockDiag A B) =
      twoBlockDiag (matrixPower r A) (matrixPower r B) := by
  classical
  let hAnonneg : 0 ≤ A := Matrix.PosDef.nonneg hA
  let hBnonneg : 0 ≤ B := Matrix.PosDef.nonneg hB
  have hblockpd : Matrix.PosDef (twoBlockDiag A B) := twoBlockDiag_posDef hA hB
  let hblocknonneg : 0 ≤ twoBlockDiag A B := Matrix.PosDef.nonneg hblockpd
  let rawA : Fin n → ℝ := fun i => hA.1.eigenvalues i
  let rawB : Fin n → ℝ := fun i => hB.1.eigenvalues i
  let rawBlock : Fin (2 * n) → ℝ := fun i =>
    hblockpd.1.eigenvalues i
  let s : Finset ℝ :=
    (Finset.univ.image rawBlock) ∪ (Finset.univ.image rawA) ∪ (Finset.univ.image rawB)
  let q : Polynomial ℝ :=
    Lagrange.interpolate s.attach (fun x : {x // x ∈ s} => (x : ℝ))
      (fun x : {x // x ∈ s} => powerFn r (x : ℝ))
  have hinj : Set.InjOn (fun x : {x // x ∈ s} => (x : ℝ)) s.attach := by
    intro x _ y _ hxy
    exact Subtype.ext hxy
  have hq_eval : ∀ x ∈ s, Polynomial.eval x q = powerFn r x := by
    intro x hx
    have hxatt : (⟨x, hx⟩ : {x // x ∈ s}) ∈ s.attach := by simp
    simpa [q] using
      Lagrange.eval_interpolate_at_node
        (s := s.attach) (v := fun x : {x // x ∈ s} => (x : ℝ))
        (r := fun x : {x // x ∈ s} => powerFn r (x : ℝ)) hinj hxatt
  have hqBlock :
      ∀ i : Fin (2 * n), Polynomial.eval (rawBlock i) q = powerFn r (rawBlock i) := by
    intro i
    exact hq_eval (rawBlock i)
      (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_image_of_mem rawBlock (Finset.mem_univ i))))
  have hqA :
      ∀ i : Fin n, Polynomial.eval (rawA i) q = powerFn r (rawA i) := by
    intro i
    exact hq_eval (rawA i)
      (Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_image_of_mem rawA (Finset.mem_univ i))))
  have hqB :
      ∀ i : Fin n, Polynomial.eval (rawB i) q = powerFn r (rawB i) := by
    intro i
    exact hq_eval (rawB i)
      (Finset.mem_union_right _ (Finset.mem_image_of_mem rawB (Finset.mem_univ i)))
  rw [matrixPower_eq_polynomial_aeval_of_eqOn_eigenvalues_nonneg hblocknonneg r q hqBlock,
    matrixPower_eq_polynomial_aeval_of_eqOn_eigenvalues_nonneg hAnonneg r q hqA,
    matrixPower_eq_polynomial_aeval_of_eqOn_eigenvalues_nonneg hBnonneg r q hqB]
  exact polynomial_aeval_twoBlockDiag (Polynomial.map (algebraMap ℝ ℂ) q) A B

/-- Source: Hiai, proof of Theorem 6.4. -/
private theorem jInversePowerTrace_homogeneous {n : ℕ} {p r : ℝ}
    {A B X : Mₙ n} (hr : 0 < r) (hB : Matrix.PosDef B) :
    jInversePowerTrace p (r • A) (r • B) (r • X) =
      r * jInversePowerTrace p A B X := by
  have hBs : Matrix.PosDef (r • B) := matrixPosDef_smul hB hr
  rw [jInversePowerTrace_eq_jOperatorInv_powerFn_qform (p := p) hBs,
    jInversePowerTrace_eq_jOperatorInv_powerFn_qform (p := p) hB]
  rw [jOperatorInv_homogeneous (f := powerFn p) (A := A) (B := B) hr]
  change
    Complex.re
        (Matrix.trace
          (Matrix.conjTranspose ((r : ℂ) • X) *
            ((((r⁻¹ : ℝ) : ℂ) • jOperatorInv (powerFn p) A B) ((r : ℂ) • X)))) =
      r * Complex.re
        (Matrix.trace (Matrix.conjTranspose X * jOperatorInv (powerFn p) A B X))
  rw [ContinuousLinearMap.smul_apply]
  rw [map_smul]
  have hscalar : ((r⁻¹ : ℝ) : ℂ) * (r : ℂ) = 1 := by
    have hreal : r⁻¹ * r = 1 := inv_mul_cancel₀ (ne_of_gt hr)
    exact_mod_cast hreal
  simp only [smul_smul, hscalar, one_smul]
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.trace_smul]
  change
    Complex.re (star (r : ℂ) *
      Matrix.trace (Matrix.conjTranspose X * jOperatorInv (powerFn p) A B X)) =
      r * Complex.re (Matrix.trace (Matrix.conjTranspose X * jOperatorInv (powerFn p) A B X))
  rw [Complex.mul_re]
  simp

/-- Source: Hiai, proof of Theorem 6.4. -/
private theorem inverseTracePower_homogeneous {n : ℕ} {p r : ℝ}
    {A B X : Mₙ n} (hr : 0 < r) (hA : Matrix.PosDef A) (hB : Matrix.PosDef B) :
    inverseTracePower p (r • A) (r • B) (r • X) =
      r * inverseTracePower p A B X := by
  have hAs : Matrix.PosDef (r • A) := matrixPosDef_smul hA hr
  have hBs : Matrix.PosDef (r • B) := matrixPosDef_smul hB hr
  rw [← jInversePowerTrace_eq_inverseTracePower_of_posDef (p := p) hAs hBs,
    ← jInversePowerTrace_eq_inverseTracePower_of_posDef (p := p) hA hB]
  exact jInversePowerTrace_homogeneous (p := p) (A := A) (B := B) (X := X) hr hB

/-- Source: Hiai, proof of Theorem 6.4. -/
private theorem inverseTracePower_twoBlockDiag {n : ℕ} {p : ℝ}
    {A₁ A₂ B₁ B₂ X₁ X₂ : Mₙ n}
    (hA₁ : Matrix.PosDef A₁) (hA₂ : Matrix.PosDef A₂)
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂) :
    inverseTracePower p (twoBlockDiag A₁ A₂) (twoBlockDiag B₁ B₂)
        (twoBlockDiag X₁ X₂) =
      inverseTracePower p A₁ B₁ X₁ + inverseTracePower p A₂ B₂ X₂ := by
  rw [inverseTracePower, inverseTracePower, inverseTracePower, powerTrace, powerTrace, powerTrace]
  rw [matrixPower_twoBlockDiag_posDef (r := -p) hA₁ hA₂,
    matrixPower_twoBlockDiag_posDef (r := p - 1) hB₁ hB₂,
    conjTranspose_twoBlockDiag]
  rw [twoBlockDiag_mul, twoBlockDiag_mul, twoBlockDiag_mul]
  rw [trace_twoBlockDiag]
  simp [Complex.add_re]

/-- Source: Hiai, proof of Theorem 6.4. -/
private theorem inverseTracePower_twoBlockDiag_weighted {n : ℕ} {p t : ℝ}
    {A₁ A₂ B₁ B₂ X₁ X₂ : Mₙ n}
    (ht0 : 0 < t) (ht1 : t < 1)
    (hA₁ : Matrix.PosDef A₁) (hA₂ : Matrix.PosDef A₂)
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂) :
    inverseTracePower p (twoBlockDiag (t • A₁) ((1 - t) • A₂))
        (twoBlockDiag (t • B₁) ((1 - t) • B₂))
        (twoBlockDiag (t • X₁) ((1 - t) • X₂)) =
      t * inverseTracePower p A₁ B₁ X₁ +
        (1 - t) * inverseTracePower p A₂ B₂ X₂ := by
  have h1t : 0 < 1 - t := sub_pos.mpr ht1
  rw [inverseTracePower_twoBlockDiag
    (hA₁ := matrixPosDef_smul hA₁ ht0) (hA₂ := matrixPosDef_smul hA₂ h1t)
    (hB₁ := matrixPosDef_smul hB₁ ht0) (hB₂ := matrixPosDef_smul hB₂ h1t)]
  rw [inverseTracePower_homogeneous (p := p) (r := t) ht0 hA₁ hB₁,
    inverseTracePower_homogeneous (p := p) (r := 1 - t) h1t hA₂ hB₂]

/-- Source: Hiai, proof of Theorem 6.4. -/
theorem powerTrace_tendsto_exponents_posDef {α : Type*} {n : ℕ}
    {A B X : Mₙ n} (hA : Matrix.PosDef A) (hB : Matrix.PosDef B)
    {l : Filter α} {r s : α → ℝ} {r₀ s₀ : ℝ}
    (hr : Filter.Tendsto r l (𝓝 r₀)) (hs : Filter.Tendsto s l (𝓝 s₀)) :
    Filter.Tendsto (fun a : α => powerTrace (r a) (s a) A B X) l
      (𝓝 (powerTrace r₀ s₀ A B X)) := by
  have hApow :
      Filter.Tendsto (fun a : α => matrixPower (r a) A) l (𝓝 (matrixPower r₀ A)) :=
    _root_.HiaiPetz.matrixPower_tendsto_exponent_of_posDef hA hr
  have hBpow :
      Filter.Tendsto (fun a : α => matrixPower (s a) B) l (𝓝 (matrixPower s₀ B)) :=
    _root_.HiaiPetz.matrixPower_tendsto_exponent_of_posDef hB hs
  have hprod :
      Filter.Tendsto
        (fun a : α =>
          Matrix.conjTranspose X * matrixPower (r a) A * X * matrixPower (s a) B)
        l
        (𝓝 (Matrix.conjTranspose X * matrixPower r₀ A * X * matrixPower s₀ B)) := by
    exact ((tendsto_const_nhds.mul hApow).mul tendsto_const_nhds).mul hBpow
  have htrace :
      Filter.Tendsto
        (fun a : α =>
          Matrix.trace (Matrix.conjTranspose X * matrixPower (r a) A * X *
            matrixPower (s a) B))
        l
        (𝓝 (Matrix.trace
          (Matrix.conjTranspose X * matrixPower r₀ A * X * matrixPower s₀ B))) := by
    have hcont : Continuous (fun M : Mₙ n => Matrix.trace M) := by
      dsimp [Matrix.trace]
      fun_prop
    exact hcont.continuousAt.tendsto.comp hprod
  simpa [powerTrace] using Complex.continuous_re.continuousAt.tendsto.comp htrace

/-- Source: Hiai, proof of Theorem 6.4. -/
theorem powerTrace_right_comp_posDef {n : ℕ} {a r s : ℝ}
    {A B X : Mₙ n} (hB : Matrix.PosDef B) :
    powerTrace a s A (matrixPower r B) X =
      powerTrace a (r * s) A B X := by
  simp [powerTrace, matrixPower_comp_posDef (s := s) hB]

/-- Source: Hiai, proof of Theorem 6.4. -/
private theorem powerTrace_left_comp_posDef {n : ℕ} {a r s : ℝ}
    {A B X : Mₙ n} (hA : Matrix.PosDef A) :
    powerTrace s a (matrixPower r A) B X =
      powerTrace (r * s) a A B X := by
  simp [powerTrace, matrixPower_comp_posDef (s := s) hA]

/-- Source: Hiai, proof of Theorem 6.4. -/
theorem powerTrace_le_of_right_power_le_posDef {n : ℕ} {r s : ℝ}
    {A B1 B2 X : Mₙ n} (hA : Matrix.PosDef A)
    (hle : matrixPower s B1 ≤ matrixPower s B2) :
    powerTrace r s A B1 X ≤ powerTrace r s A B2 X := by
  let Ar : Mₙ n := matrixPower r A
  let D : Mₙ n := matrixPower s B2 - matrixPower s B1
  have hAr_nonneg : 0 ≤ Ar := by
    simpa [Ar] using Matrix.PosDef.nonneg (matrixPower_posDef_of_posDef (r := r) hA)
  have hC_nonneg : 0 ≤ Matrix.conjTranspose X * Ar * X := by
    have hAr_psd : Ar.PosSemidef := (Matrix.nonneg_iff_posSemidef).mp hAr_nonneg
    exact (Matrix.nonneg_iff_posSemidef).mpr
      (Matrix.PosSemidef.conjTranspose_mul_mul_same hAr_psd X)
  have hD_nonneg : 0 ≤ D := by
    simpa [D] using sub_nonneg.mpr hle
  have htrace :
      0 ≤ Complex.re (Matrix.trace ((Matrix.conjTranspose X * Ar * X) * D)) :=
    re_trace_mul_nonneg_of_nonneg_nonneg hC_nonneg hD_nonneg
  rw [← sub_nonneg]
  have hdiff :
      powerTrace r s A B2 X - powerTrace r s A B1 X =
        Complex.re (Matrix.trace ((Matrix.conjTranspose X * Ar * X) * D)) := by
    have hmat :
        Matrix.conjTranspose X * matrixPower r A * X * matrixPower s B2 -
            Matrix.conjTranspose X * matrixPower r A * X * matrixPower s B1 =
          (Matrix.conjTranspose X * Ar * X) * D := by
      simp [Ar, D, Matrix.mul_assoc, sub_eq_add_neg, Matrix.mul_add]
    calc
      powerTrace r s A B2 X - powerTrace r s A B1 X
          = Complex.re
              (Matrix.trace
                (Matrix.conjTranspose X * matrixPower r A * X * matrixPower s B2)) -
            Complex.re
              (Matrix.trace
                (Matrix.conjTranspose X * matrixPower r A * X * matrixPower s B1)) := by
              rfl
      _ = Complex.re
            (Matrix.trace
              (Matrix.conjTranspose X * matrixPower r A * X * matrixPower s B2) -
              Matrix.trace
                (Matrix.conjTranspose X * matrixPower r A * X * matrixPower s B1)) := by
            rw [Complex.sub_re]
      _ = Complex.re
            (Matrix.trace
              (Matrix.conjTranspose X * matrixPower r A * X * matrixPower s B2 -
                Matrix.conjTranspose X * matrixPower r A * X * matrixPower s B1)) := by
            rw [Matrix.trace_sub]
      _ = Complex.re (Matrix.trace ((Matrix.conjTranspose X * Ar * X) * D)) := by
            rw [hmat]
  simpa [hdiff] using htrace

/-- Source: Hiai, proof of Theorem 6.4. -/
private theorem powerTrace_le_of_left_power_le_posDef {n : ℕ} {r s : ℝ}
    {A1 A2 B X : Mₙ n} (hB : Matrix.PosDef B)
    (hle : matrixPower r A1 ≤ matrixPower r A2) :
    powerTrace r s A1 B X ≤ powerTrace r s A2 B X := by
  let Br : Mₙ n := matrixPower s B
  let D : Mₙ n := matrixPower r A2 - matrixPower r A1
  have hBr_nonneg : 0 ≤ Br := by
    simpa [Br] using Matrix.PosDef.nonneg (matrixPower_posDef_of_posDef (r := s) hB)
  have hD_nonneg : 0 ≤ D := by
    simpa [D] using sub_nonneg.mpr hle
  have hC_nonneg : 0 ≤ Matrix.conjTranspose X * D * X := by
    have hD_psd : D.PosSemidef := (Matrix.nonneg_iff_posSemidef).mp hD_nonneg
    exact (Matrix.nonneg_iff_posSemidef).mpr
      (Matrix.PosSemidef.conjTranspose_mul_mul_same hD_psd X)
  have htrace :
      0 ≤ Complex.re (Matrix.trace ((Matrix.conjTranspose X * D * X) * Br)) :=
    re_trace_mul_nonneg_of_nonneg_nonneg hC_nonneg hBr_nonneg
  rw [← sub_nonneg]
  have hdiff :
      powerTrace r s A2 B X - powerTrace r s A1 B X =
        Complex.re (Matrix.trace ((Matrix.conjTranspose X * D * X) * Br)) := by
    have hmat :
        Matrix.conjTranspose X * matrixPower r A2 * X * matrixPower s B -
            Matrix.conjTranspose X * matrixPower r A1 * X * matrixPower s B =
          (Matrix.conjTranspose X * D * X) * Br := by
      ext i j
      simp only [Br, D, sub_eq_add_neg, Matrix.add_mul, Matrix.mul_add, Matrix.neg_mul,
        Matrix.mul_neg]
    calc
      powerTrace r s A2 B X - powerTrace r s A1 B X
          = Complex.re
              (Matrix.trace
                (Matrix.conjTranspose X * matrixPower r A2 * X * matrixPower s B)) -
            Complex.re
              (Matrix.trace
                (Matrix.conjTranspose X * matrixPower r A1 * X * matrixPower s B)) := by
              rfl
      _ = Complex.re
            (Matrix.trace
              (Matrix.conjTranspose X * matrixPower r A2 * X * matrixPower s B) -
              Matrix.trace
                (Matrix.conjTranspose X * matrixPower r A1 * X * matrixPower s B)) := by
            rw [Complex.sub_re]
      _ = Complex.re
            (Matrix.trace
              (Matrix.conjTranspose X * matrixPower r A2 * X * matrixPower s B -
                Matrix.conjTranspose X * matrixPower r A1 * X * matrixPower s B)) := by
            rw [Matrix.trace_sub]
      _ = Complex.re (Matrix.trace ((Matrix.conjTranspose X * D * X) * Br)) := by
            rw [hmat]
  simpa [hdiff] using htrace

/-- Source: Hiai, Theorem 6.4. -/
private theorem powerTrace_neg_p_p_sub_one_jointlyConvex :
    ∀ {n : ℕ} {p : ℝ},
      p ∈ Set.Icc (0 : ℝ) 1 →
      ∀ {A1 A2 B1 B2 X1 X2 : Mₙ n} {t : ℝ},
        t ∈ Set.Icc (0 : ℝ) 1 →
        Matrix.PosDef A1 →
        Matrix.PosDef A2 →
        Matrix.PosDef B1 →
        Matrix.PosDef B2 →
        powerTrace (-p) (p - 1) (t • A1 + (1 - t) • A2)
            (t • B1 + (1 - t) • B2) (t • X1 + (1 - t) • X2) ≤
          t * powerTrace (-p) (p - 1) A1 B1 X1 +
            (1 - t) * powerTrace (-p) (p - 1) A2 B2 X2 := by
  intro n p hp A1 A2 B1 B2 X1 X2 t ht hA1 hA2 hB1 hB2
  by_cases htzero : t = 0
  · subst t
    have hA : (0 : ℝ) • A1 + (1 : ℝ) • A2 = A2 := by
      ext i j
      simp
    have hB : (0 : ℝ) • B1 + (1 : ℝ) • B2 = B2 := by
      ext i j
      simp
    have hX : (0 : ℝ) • X1 + (1 : ℝ) • X2 = X2 := by
      ext i j
      simp
    simp only [sub_zero]
    rw [hA, hB, hX, zero_mul, one_mul, zero_add]
  by_cases htone : t = 1
  · subst t
    have hA : (1 : ℝ) • A1 + (0 : ℝ) • A2 = A1 := by
      ext i j
      simp
    have hB : (1 : ℝ) • B1 + (0 : ℝ) • B2 = B1 := by
      ext i j
      simp
    have hX : (1 : ℝ) • X1 + (0 : ℝ) • X2 = X1 := by
      ext i j
      simp
    simp only [sub_self]
    rw [hA, hB, hX, zero_mul, one_mul, add_zero]
  have ht0 : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm htzero)
  have ht1 : t < 1 := lt_of_le_of_ne ht.2 htone
  let Ablock : Mₙ (2 * n) := twoBlockDiag (t • A1) ((1 - t) • A2)
  let Bblock : Mₙ (2 * n) := twoBlockDiag (t • B1) ((1 - t) • B2)
  let Xblock : Mₙ (2 * n) := twoBlockDiag (t • X1) ((1 - t) • X2)
  have hAblock : Matrix.PosDef Ablock := by
    dsimp [Ablock]
    exact twoBlockDiag_posDef (matrixPosDef_smul hA1 ht0)
      (matrixPosDef_smul hA2 (sub_pos.mpr ht1))
  have hBblock : Matrix.PosDef Bblock := by
    dsimp [Bblock]
    exact twoBlockDiag_posDef (matrixPosDef_smul hB1 ht0)
      (matrixPosDef_smul hB2 (sub_pos.mpr ht1))
  have hmain :=
    TraceMonotonicity.inverseTracePowerStrictlyPositive (blockSumMap n)
      (p := p) (A := Ablock) (B := Bblock) (X := Xblock)
      hp (blockSumMap_positive n) (blockSumMap_tracePreserving n)
      (blockSumMap_hsAdjointSchwarz n)
      hAblock hBblock (blockSumMap_one_posDef n)
  have hsplit :
      inverseTracePower p Ablock Bblock Xblock =
        t * inverseTracePower p A1 B1 X1 +
          (1 - t) * inverseTracePower p A2 B2 X2 := by
    dsimp [Ablock, Bblock, Xblock]
    exact inverseTracePower_twoBlockDiag_weighted
      (p := p) ht0 ht1 hA1 hA2 hB1 hB2
  have hAsum : blockSumMap n Ablock = t • A1 + (1 - t) • A2 := blockSumMap_twoBlockDiag _ _
  have hBsum : blockSumMap n Bblock = t • B1 + (1 - t) • B2 := blockSumMap_twoBlockDiag _ _
  have hXsum : blockSumMap n Xblock = t • X1 + (1 - t) • X2 := blockSumMap_twoBlockDiag _ _
  rw [hAsum, hBsum, hXsum] at hmain
  dsimp [inverseTracePower] at hmain hsplit
  calc
    powerTrace (-p) (p - 1) (t • A1 + (1 - t) • A2)
        (t • B1 + (1 - t) • B2) (t • X1 + (1 - t) • X2)
        ≤ powerTrace (-p) (p - 1) Ablock Bblock Xblock := hmain
    _ = t * powerTrace (-p) (p - 1) A1 B1 X1 +
        (1 - t) * powerTrace (-p) (p - 1) A2 B2 X2 := hsplit

/-- Source: Hiai, Theorem 6.4.

`inverseTracePower p` is represented internally as `powerTrace (-p) (p - 1)`. -/
theorem inverseTracePower_jointlyConvex :
    ∀ {n : ℕ} {p : ℝ},
      p ∈ Set.Icc (0 : ℝ) 1 →
      ∀ {A1 A2 B1 B2 X1 X2 : Mₙ n} {t : ℝ},
        t ∈ Set.Icc (0 : ℝ) 1 →
        Matrix.PosDef A1 →
        Matrix.PosDef A2 →
        Matrix.PosDef B1 →
        Matrix.PosDef B2 →
        inverseTracePower p (t • A1 + (1 - t) • A2)
            (t • B1 + (1 - t) • B2) (t • X1 + (1 - t) • X2) ≤
          t * inverseTracePower p A1 B1 X1 +
            (1 - t) * inverseTracePower p A2 B2 X2 := by
  intro n p hp A1 A2 B1 B2 X1 X2 t ht hA1 hA2 hB1 hB2
  simpa [inverseTracePower] using
    (powerTrace_neg_p_p_sub_one_jointlyConvex
      (p := p) hp (t := t) ht hA1 hA2 hB1 hB2 (X1 := X1) (X2 := X2))

end MatrixScopedInstances

end TraceConvexity

end HiaiPetz
