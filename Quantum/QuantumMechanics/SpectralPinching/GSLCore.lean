import Quantum.QuantumMechanics.QuantumChannelCompat.GSLCoreGeneralizedStein
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

/-!
# Spectral pinching channels

This file constructs the canonical pinching channel of a finite-dimensional
self-adjoint operator from its distinct eigenspaces.  The construction uses
orthogonal projections onto eigenspaces, so it does not depend on a choice of
eigenbasis.
-/

namespace QuantumChannel

open QuantumState

universe u

noncomputable section

variable {H : Type u} [Qudit H]

/-- The finite type of distinct eigenvalues of an operator. -/
abbrev spectralEigenvalue (A : L H) := Module.End.Eigenvalues A

/-- The canonical orthogonal projector onto one eigenspace. -/
noncomputable def spectralProjector (A : L H) (mu : spectralEigenvalue A) : L H :=
  (Module.End.eigenspace A mu.1).starProjection.toLinearMap

/-- A spectral projector is self-adjoint. -/
theorem spectralProjector_isSymmetric (A : L H) (mu : spectralEigenvalue A) :
    (spectralProjector A mu).IsSymmetric := by
  simpa [spectralProjector] using
    (Submodule.starProjection_isSymmetric (Module.End.eigenspace A mu.1))

/-- A spectral projector is idempotent. -/
theorem spectralProjector_isIdempotentElem (A : L H) (mu : spectralEigenvalue A) :
    IsIdempotentElem (spectralProjector A mu) := by
  simpa [spectralProjector] using
    (Submodule.isSymmetricProjection_starProjection
      (Module.End.eigenspace A mu.1)).isIdempotentElem

/-- The range of the canonical spectral projector is its eigenspace. -/
@[simp]
theorem spectralProjector_range (A : L H) (mu : spectralEigenvalue A) :
    LinearMap.range (spectralProjector A mu) = Module.End.eigenspace A mu.1 := by
  simp [spectralProjector]

/-- Projectors belonging to distinct eigenvalues have zero product. -/
theorem spectralProjector_mul_eq_zero
    (A : L H) (hA : A.IsSymmetric) {mu nu : spectralEigenvalue A}
    (hmunu : mu ≠ nu) :
    spectralProjector A mu * spectralProjector A nu = 0 := by
  ext x
  change spectralProjector A mu (spectralProjector A nu x) = 0
  have hxnu : spectralProjector A nu x ∈ Module.End.eigenspace A nu.1 := by
    rw [← spectralProjector_range A nu]
    exact LinearMap.mem_range_self (spectralProjector A nu) x
  have hxorth : spectralProjector A nu x ∈ (Module.End.eigenspace A mu.1)ᗮ :=
    hA.orthogonalFamily_eigenspaces'.isOrtho hmunu.symm hxnu
  simpa [spectralProjector] using
    ((Submodule.starProjection_apply_eq_zero_iff
      (K := Module.End.eigenspace A mu.1)).2 hxorth)

/-- The distinct spectral projectors resolve the identity. -/
theorem spectralProjector_sum_eq_one (A : L H) (hA : A.IsSymmetric) :
    ∑ mu : spectralEigenvalue A, spectralProjector A mu = 1 := by
  ext x
  simp only [LinearMap.sum_apply]
  change (∑ mu : spectralEigenvalue A, spectralProjector A mu x) = x
  have hx : x ∈ ⨆ mu : spectralEigenvalue A, Module.End.eigenspace A mu.1 := by
    have htop : (⨆ mu : Module.End.Eigenvalues A,
        Module.End.eigenspace A mu.1) = ⊤ :=
      hA.direct_sum_isInternal.submodule_iSup_eq_top
    rw [htop]
    exact Submodule.mem_top
  simpa [spectralProjector] using
    (hA.orthogonalFamily_eigenspaces'.sum_projection_of_mem_iSup x hx)

/-- The linear map underlying spectral pinching. -/
noncomputable def spectralPinchingLinearMap (A : L H) : T H H :=
  ∑ mu : spectralEigenvalue A, krausTerm (spectralProjector A mu)

/-- Spectral pinching acts by summing the diagonal eigenspace blocks. -/
@[simp]
theorem spectralPinchingLinearMap_apply (A X : L H) :
    spectralPinchingLinearMap A X =
      ∑ mu : spectralEigenvalue A,
        spectralProjector A mu * X * spectralProjector A mu := by
  classical
  simp only [spectralPinchingLinearMap, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro mu _
  change spectralProjector A mu * X * LinearMap.adjoint (spectralProjector A mu) =
    spectralProjector A mu * X * spectralProjector A mu
  rw [(spectralProjector_isSymmetric A mu).adjoint_eq]

/-- The spectral pinching map of a self-adjoint operator, bundled as a CPTP
channel. -/
noncomputable def spectralPinchingChannel (A : L H) (hA : A.IsSymmetric) : CPTP H H where
  toFun := spectralPinchingLinearMap A
  map_add' := (spectralPinchingLinearMap A).map_add
  map_smul' := (spectralPinchingLinearMap A).map_smul
  map_cstarMatrix_nonneg' k M hM := by
    exact (isCompletelyPositive_iff_cstarMatrix_nonneg _).mp
      (sum_krausTerm_isCompletelyPositive (fun mu : spectralEigenvalue A =>
        spectralProjector A mu)) k M hM
  trace_map X := by
    rw [spectralPinchingLinearMap_apply, map_sum]
    calc
      Tr X = Tr ((∑ mu : spectralEigenvalue A, spectralProjector A mu) * X) := by
        rw [spectralProjector_sum_eq_one A hA, one_mul]
      _ = ∑ mu : spectralEigenvalue A, Tr (spectralProjector A mu * X) := by
        rw [Finset.sum_mul, map_sum]
      _ = ∑ mu : spectralEigenvalue A,
          Tr (spectralProjector A mu * X * spectralProjector A mu) := by
        apply Finset.sum_congr rfl
        intro mu _
        symm
        rw [LinearMap.trace_mul_cycle,
          spectralProjector_isIdempotentElem A mu]

/-- Exact action of the bundled spectral pinching channel. -/
@[simp]
theorem spectralPinchingChannel_apply
    (A : L H) (hA : A.IsSymmetric) (X : L H) :
    (spectralPinchingChannel A hA).toFun X =
      ∑ mu : spectralEigenvalue A,
        spectralProjector A mu * X * spectralProjector A mu := by
  exact spectralPinchingLinearMap_apply A X

/-- The bundled pinching channel preserves trace. -/
@[simp]
theorem spectralPinchingChannel_trace
    (A : L H) (hA : A.IsSymmetric) (X : L H) :
    Tr ((spectralPinchingChannel A hA).toFun X) = Tr X := by
  exact (spectralPinchingChannel A hA).trace_map X |>.symm

/-! ## commutation and fixed points -/

/-- A self-adjoint operator acts by its eigenvalue on the range of the
corresponding spectral projector. -/
theorem mul_spectralProjector
    (A : L H) (mu : spectralEigenvalue A) :
    A * spectralProjector A mu = mu.1 • spectralProjector A mu := by
  ext x
  change A (spectralProjector A mu x) = mu.1 • spectralProjector A mu x
  apply Module.End.mem_eigenspace_iff.mp
  rw [← spectralProjector_range A mu]
  exact LinearMap.mem_range_self (spectralProjector A mu) x

/-- A spectral projector also acts on the left of its self-adjoint operator
by the corresponding eigenvalue. -/
theorem spectralProjector_mul
    (A : L H) (hA : A.IsSymmetric) (mu : spectralEigenvalue A) :
    spectralProjector A mu * A = mu.1 • spectralProjector A mu := by
  calc
    spectralProjector A mu * A =
        LinearMap.adjoint (A * spectralProjector A mu) := by
      change spectralProjector A mu ∘ₗ A =
        LinearMap.adjoint (A ∘ₗ spectralProjector A mu)
      rw [LinearMap.adjoint_comp, hA.adjoint_eq,
        (spectralProjector_isSymmetric A mu).adjoint_eq]
    _ = LinearMap.adjoint (mu.1 • spectralProjector A mu) := by
      rw [mul_spectralProjector]
    _ = (starRingEnd ℂ) mu.1 • spectralProjector A mu := by
      rw [map_smulₛₗ, (spectralProjector_isSymmetric A mu).adjoint_eq]
    _ = mu.1 • spectralProjector A mu := by
      rw [hA.conj_eigenvalue_eq_self mu.2]

/-- Every pinched operator commutes with the self-adjoint operator defining
the spectral blocks. -/
theorem spectralPinchingChannel_commute
    (A : L H) (hA : A.IsSymmetric) (X : L H) :
    Commute ((spectralPinchingChannel A hA).toFun X) A := by
  change (spectralPinchingChannel A hA).toFun X * A =
    A * (spectralPinchingChannel A hA).toFun X
  rw [spectralPinchingChannel_apply, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro mu _
  calc
    (spectralProjector A mu * X * spectralProjector A mu) * A =
        spectralProjector A mu * X * (spectralProjector A mu * A) := by
      rw [mul_assoc]
    _ = spectralProjector A mu * X *
        (mu.1 • spectralProjector A mu) := by
      rw [spectralProjector_mul A hA mu]
    _ = mu.1 • (spectralProjector A mu * X * spectralProjector A mu) := by
      rw [mul_smul_comm]
    _ = (mu.1 • spectralProjector A mu) * X * spectralProjector A mu := by
      rw [smul_mul_assoc, smul_mul_assoc]
    _ = (A * spectralProjector A mu) * X * spectralProjector A mu := by
      rw [mul_spectralProjector A mu]
    _ = A * (spectralProjector A mu * X * spectralProjector A mu) := by
      simp only [mul_assoc]

/-- An operator commuting with `A` preserves every eigenspace of `A`. -/
theorem mapsTo_eigenspace_of_commute
    {A X : L H} (hXA : Commute X A) (mu : ℂ) :
    Set.MapsTo X (Module.End.eigenspace A mu) (Module.End.eigenspace A mu) := by
  intro x hx
  change X x ∈ Module.End.eigenspace A mu
  change x ∈ Module.End.eigenspace A mu at hx
  rw [Module.End.mem_eigenspace_iff] at hx ⊢
  calc
    A (X x) = X (A x) := by
      change (A * X) x = (X * A) x
      rw [hXA.eq]
    _ = mu • X x := by rw [hx, map_smul]

/-- If `X` commutes with `A`, then each diagonal spectral block is `X P_mu`. -/
theorem spectralProjector_mul_mul_of_commute
    (A X : L H) (hXA : Commute X A) (mu : spectralEigenvalue A) :
    spectralProjector A mu * X * spectralProjector A mu =
      X * spectralProjector A mu := by
  ext x
  change spectralProjector A mu (X (spectralProjector A mu x)) =
    X (spectralProjector A mu x)
  have hP : spectralProjector A mu x ∈ Module.End.eigenspace A mu.1 := by
    rw [← spectralProjector_range A mu]
    exact LinearMap.mem_range_self (spectralProjector A mu) x
  have hXP := mapsTo_eigenspace_of_commute hXA mu.1 hP
  simpa [spectralProjector] using
    (Submodule.starProjection_mem_subspace_eq_self
      (⟨X (spectralProjector A mu x), hXP⟩ : Module.End.eigenspace A mu.1))

/-- Spectral pinching fixes exactly the operators commuting with its
self-adjoint reference operator. -/
theorem spectralPinchingChannel_eq_iff_commute
    (A : L H) (hA : A.IsSymmetric) (X : L H) :
    (spectralPinchingChannel A hA).toFun X = X ↔ Commute X A := by
  constructor
  · intro hfix
    rw [← hfix]
    exact spectralPinchingChannel_commute A hA X
  · intro hXA
    rw [spectralPinchingChannel_apply]
    calc
      (∑ mu : spectralEigenvalue A,
          spectralProjector A mu * X * spectralProjector A mu) =
          ∑ mu : spectralEigenvalue A, X * spectralProjector A mu := by
            apply Finset.sum_congr rfl
            intro mu _
            exact spectralProjector_mul_mul_of_commute A X hXA mu
      _ = X * ∑ mu : spectralEigenvalue A, spectralProjector A mu := by
        rw [Finset.mul_sum]
      _ = X := by rw [spectralProjector_sum_eq_one A hA, mul_one]

/-! ### Complete dephasing in an orthonormal basis -/

/-- A spectral projector is the identity on its eigenspace. -/
theorem spectralProjector_apply_of_mem_eigenspace
    (A : L H) (mu : spectralEigenvalue A) {x : H}
    (hx : x ∈ Module.End.eigenspace A mu.1) :
    spectralProjector A mu x = x := by
  simpa [spectralProjector] using
    (Submodule.starProjection_mem_subspace_eq_self
      (⟨x, hx⟩ : Module.End.eigenspace A mu.1))

/-- A spectral projector kills vectors in a distinct eigenspace. -/
theorem spectralProjector_apply_eq_zero_of_mem_eigenspace
    (A : L H) (hA : A.IsSymmetric)
    {mu nu : spectralEigenvalue A} (hmunu : mu ≠ nu) {x : H}
    (hx : x ∈ Module.End.eigenspace A nu.1) :
    spectralProjector A mu x = 0 := by
  have hxorth : x ∈ (Module.End.eigenspace A mu.1)ᗮ :=
    hA.orthogonalFamily_eigenspaces'.isOrtho hmunu.symm hx
  simpa [spectralProjector] using
    ((Submodule.starProjection_apply_eq_zero_iff
      (K := Module.End.eigenspace A mu.1)).2 hxorth)

/-- Spectral pinching preserves the diagonal coefficient of every vector in
one spectral subspace. -/
theorem inner_spectralPinching_eq_of_mem_eigenspace
    (A : L H) (hA : A.IsSymmetric) (X : L H)
    (mu : spectralEigenvalue A) {x : H}
    (hx : x ∈ Module.End.eigenspace A mu.1) :
    inner ℂ x ((spectralPinchingChannel A hA).toFun X x) = inner ℂ x (X x) := by
  rw [spectralPinchingChannel_apply, LinearMap.sum_apply]
  change inner ℂ x
    (∑ nu : spectralEigenvalue A,
      spectralProjector A nu (X (spectralProjector A nu x))) = inner ℂ x (X x)
  rw [inner_sum]
  classical
  rw [Finset.sum_eq_single mu]
  · rw [spectralProjector_apply_of_mem_eigenspace A mu hx]
    rw [← (spectralProjector_isSymmetric A mu) x (X x)]
    rw [spectralProjector_apply_of_mem_eigenspace A mu hx]
  · intro nu _ hnumu
    have hzero := spectralProjector_apply_eq_zero_of_mem_eigenspace
      A hA hnumu hx
    simp [hzero]
  · intro hmu
    exact (hmu (Finset.mem_univ mu)).elim

/-! ### Common eigenbasis and dephasing witness -/

/-- Spectral pinching sends density operators to density operators. -/
theorem spectralPinchingChannel_isDensity
    (A : L H) (hA : A.IsSymmetric) (rho : L H) (hrho : IsDensity rho) :
    IsDensity ((spectralPinchingChannel A hA).toFun rho) := by
  constructor
  · apply (LinearMap.nonneg_iff_isPositive _).mp
    exact map_nonneg (spectralPinchingChannel A hA).toCompletelyPositiveMap
      ((LinearMap.nonneg_iff_isPositive rho).mpr hrho.1)
  · rw [spectralPinchingChannel_trace, hrho.2]

/-- The joint eigenspaces of two density operators form an orthogonal
family, indexed only by their actual eigenvalues. -/
theorem densityJointOrthogonalFamily
    (R S : L H) (hR : IsDensity R) (hS : IsDensity S) :
    OrthogonalFamily ℂ
      (fun (i : Module.End.Eigenvalues R × Module.End.Eigenvalues S) =>
        (Module.End.eigenspace R i.1.1 ⊓ Module.End.eigenspace S i.2.1 :
          Submodule ℂ H))
      (fun i => (Module.End.eigenspace R i.1.1 ⊓
        Module.End.eigenspace S i.2.1).subtypeₗᵢ) := by
  exact (hR.1.isSymmetric.orthogonalFamily_eigenspace_inf_eigenspace
    hS.1.isSymmetric).comp
      (f := fun i : Module.End.Eigenvalues R × Module.End.Eigenvalues S =>
        (i.2.1, i.1.1)) (by
      rintro ⟨r, s⟩ ⟨r', s'⟩ hij
      simp only [Prod.mk.injEq] at hij ⊢
      exact ⟨Subtype.ext hij.2, Subtype.ext hij.1⟩)

/-- The actual joint eigenspaces of commuting density operators exhaust the
whole space. -/
theorem densityJointIsInternal
    (R S : L H) (hR : IsDensity R) (hS : IsDensity S)
    (hcomm : Commute R S) :
    DirectSum.IsInternal
      (fun (i : Module.End.Eigenvalues R × Module.End.Eigenvalues S) =>
        Module.End.eigenspace R i.1.1 ⊓ Module.End.eigenspace S i.2.1) := by
  let hRs := hR.1.isSymmetric
  let hSs := hS.1.isSymmetric
  apply (densityJointOrthogonalFamily R S hR hS).isInternal_iff.mpr
  rw [Submodule.orthogonal_eq_bot_iff]
  apply top_unique
  rw [← hRs.iSup_iSup_eigenspace_inf_eigenspace_eq_top_of_commute hSs hcomm]
  refine iSup_le fun r => iSup_le fun s => ?_
  by_cases hr : Module.End.eigenspace R r = ⊥
  · simp [hr]
  by_cases hs : Module.End.eigenspace S s = ⊥
  · simp [hs]
  exact le_iSup_of_le
    (⟨⟨r, hr⟩, ⟨s, hs⟩⟩ :
      Module.End.Eigenvalues R × Module.End.Eigenvalues S) le_rfl

/-- A common orthonormal eigenbasis of two commuting density operators. -/
noncomputable def densityJointBasis
    (R S : L H) (hR : IsDensity R) (hS : IsDensity S)
    (hcomm : Commute R S) :
    OrthonormalBasis (Fin (Module.finrank ℂ H)) ℂ H :=
  (densityJointIsInternal R S hR hS hcomm).subordinateOrthonormalBasis rfl
    (densityJointOrthogonalFamily R S hR hS)

/-- The joint eigenspace containing one vector of `densityJointBasis`. -/
noncomputable def densityJointIndex
    (R S : L H) (hR : IsDensity R) (hS : IsDensity S)
    (hcomm : Commute R S) (i : Fin (Module.finrank ℂ H)) :
    Module.End.Eigenvalues R × Module.End.Eigenvalues S :=
  (densityJointIsInternal R S hR hS hcomm).subordinateOrthonormalBasisIndex
    rfl i (densityJointOrthogonalFamily R S hR hS)

/-- Membership of a common-basis vector in its recorded joint eigenspace. -/
theorem densityJointBasis_mem
    (R S : L H) (hR : IsDensity R) (hS : IsDensity S)
    (hcomm : Commute R S) (i : Fin (Module.finrank ℂ H)) :
    densityJointBasis R S hR hS hcomm i ∈
      Module.End.eigenspace R (densityJointIndex R S hR hS hcomm i).1.1 ⊓
        Module.End.eigenspace S (densityJointIndex R S hR hS hcomm i).2.1 := by
  exact (densityJointIsInternal R S hR hS hcomm)
    |>.subordinateOrthonormalBasis_subordinate rfl i
      (densityJointOrthogonalFamily R S hR hS)

/-! ### Preservation of support mismatch -/

/-- For a non-negative operator, a vanishing quadratic form forces the
operator to vanish on that vector. -/
theorem nonneg_apply_eq_zero_of_re_inner_eq_zero
    {A : L H} (hA : 0 ≤ A) {x : H}
    (hinner : RCLike.re (inner ℂ (A x) x) = 0) :
    A x = 0 := by
  let s : L H := CFC.sqrt A
  have hs_sq : s * s = A := CFC.sqrt_mul_sqrt_self A
  have hs_sym : s.IsSymmetric :=
    ((LinearMap.nonneg_iff_isPositive s).mp (CFC.sqrt_nonneg A)).isSymmetric
  have hs_apply : s (s x) = A x := by
    change (s * s) x = A x
    rw [hs_sq]
  have hnorm : ‖s x‖ ^ 2 = RCLike.re (inner ℂ (A x) x) := by
    have hinner' : inner ℂ (s x) (s x) = inner ℂ (A x) x := by
      calc
        inner ℂ (s x) (s x) = inner ℂ (s (s x)) x :=
          (hs_sym (s x) x).symm
        _ = inner ℂ (A x) x := by rw [hs_apply]
    rw [← @inner_self_eq_norm_sq ℂ H, hinner']
  rw [hinner] at hnorm
  have hsx : s x = 0 := by
    apply norm_eq_zero.mp
    exact pow_eq_zero_iff two_ne_zero |>.mp hnorm
  rw [← hs_apply, hsx, LinearMap.map_zero]

/-- If the support of `rho` is not contained in that of `sigma`, pinching
`rho` by the spectral blocks of `sigma` does not repair the mismatch. -/
theorem spectralPinching_not_supportLE
    (rho sigma : L H) (hrho : IsDensity rho) (hsigma : IsDensity sigma)
    (hmismatch : ¬ LinearMap.ker sigma ≤ LinearMap.ker rho) :
    ¬ LinearMap.ker sigma ≤
      LinearMap.ker ((spectralPinchingChannel sigma hsigma.1.isSymmetric).toFun rho) := by
  intro hpinched
  apply hmismatch
  intro x hxsigma
  rw [LinearMap.mem_ker] at hxsigma ⊢
  by_cases hx : x = 0
  · simp [hx]
  have hxeigen : x ∈ Module.End.eigenspace sigma 0 := by
    rw [Module.End.mem_eigenspace_iff]
    simpa using hxsigma
  let mu0 : spectralEigenvalue sigma :=
    ⟨0, Module.End.hasEigenvalue_of_hasEigenvector ⟨hxeigen, hx⟩⟩
  have hpinchedx :
      (spectralPinchingChannel sigma hsigma.1.isSymmetric).toFun rho x = 0 :=
    LinearMap.mem_ker.mp (hpinched (LinearMap.mem_ker.mpr hxsigma))
  have hdiagonal := inner_spectralPinching_eq_of_mem_eigenspace
    sigma hsigma.1.isSymmetric rho mu0 hxeigen
  have hinnerRight : inner ℂ x (rho x) = 0 := by
    rw [hpinchedx, inner_zero_right] at hdiagonal
    exact hdiagonal.symm
  have hinnerLeft : inner ℂ (rho x) x = 0 := by
    rw [← inner_conj_symm (rho x) x, hinnerRight, map_zero]
  exact nonneg_apply_eq_zero_of_re_inner_eq_zero
    ((LinearMap.nonneg_iff_isPositive rho).mpr hrho.1) (by simp [hinnerLeft])

/-! ### Mixed-unitary representation -/

/-- The real sign selected by one Boolean phase. -/
def spectralSign
    {A : L H} (phase : spectralEigenvalue A → Bool)
    (mu : spectralEigenvalue A) : ℂ :=
  if phase mu then -1 else 1

/-- The diagonal sign operator associated with a Boolean phase assignment. -/
noncomputable def spectralSignUnitary
    (A : L H) (phase : spectralEigenvalue A → Bool) : L H :=
  ∑ mu : spectralEigenvalue A, spectralSign phase mu • spectralProjector A mu

/-- Products of two operators diagonal in the spectral-projector
decomposition multiply their coefficients pointwise. -/
theorem spectralProjector_weighted_sum_mul
    (A : L H) (hA : A.IsSymmetric)
    (c d : spectralEigenvalue A → ℂ) :
    (∑ mu : spectralEigenvalue A, c mu • spectralProjector A mu) *
        (∑ mu : spectralEigenvalue A, d mu • spectralProjector A mu) =
      ∑ mu : spectralEigenvalue A,
        (c mu * d mu) • spectralProjector A mu := by
  classical
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro mu _
  rw [Finset.mul_sum]
  rw [Finset.sum_eq_single mu]
  · rw [smul_mul_smul_comm,
      spectralProjector_isIdempotentElem A mu]
  · intro nu _ hnumu
    rw [smul_mul_smul_comm,
      spectralProjector_mul_eq_zero A hA hnumu.symm, smul_zero]
  · intro hmu
    exact (hmu (Finset.mem_univ mu)).elim

/-- A diagonal sign operator is self-adjoint. -/
theorem spectralSignUnitary_isSymmetric
    (A : L H) (phase : spectralEigenvalue A → Bool) :
    (spectralSignUnitary A phase).IsSymmetric := by
  classical
  apply LinearMap.isSymmetric_sum
  intro mu _
  apply (spectralProjector_isSymmetric A mu).smul
  cases hphase : phase mu <;> simp [spectralSign, hphase]

/-- Every diagonal sign operator is unitary. -/
theorem spectralSignUnitary_mem_unitary
    (A : L H) (hA : A.IsSymmetric)
    (phase : spectralEigenvalue A → Bool) :
    spectralSignUnitary A phase ∈ unitary (L H) := by
  apply Unitary.mem_iff.mpr
  have hstar : star (spectralSignUnitary A phase) =
      spectralSignUnitary A phase := by
    change LinearMap.adjoint (spectralSignUnitary A phase) = _
    exact (spectralSignUnitary_isSymmetric A phase).adjoint_eq
  rw [hstar]
  have hsquare : spectralSignUnitary A phase * spectralSignUnitary A phase = 1 := by
    rw [spectralSignUnitary, spectralProjector_weighted_sum_mul A hA]
    calc
      (∑ mu : spectralEigenvalue A,
          (spectralSign phase mu * spectralSign phase mu) •
            spectralProjector A mu) =
          ∑ mu : spectralEigenvalue A, spectralProjector A mu := by
        apply Finset.sum_congr rfl
        intro mu _
        cases hphase : phase mu <;> simp [spectralSign, hphase]
      _ = 1 := spectralProjector_sum_eq_one A hA
  exact ⟨hsquare, hsquare⟩

/-- Expanding a sign-unitary conjugation gives all spectral matrix blocks
with their two signs. -/
theorem spectralSignUnitary_conjugation
    (A : L H) (phase : spectralEigenvalue A → Bool) (X : L H) :
    spectralSignUnitary A phase * X * star (spectralSignUnitary A phase) =
      ∑ mu : spectralEigenvalue A, ∑ nu : spectralEigenvalue A,
        (spectralSign phase mu * spectralSign phase nu) •
          (spectralProjector A mu * X * spectralProjector A nu) := by
  classical
  have hstar : star (spectralSignUnitary A phase) =
      spectralSignUnitary A phase := by
    change LinearMap.adjoint (spectralSignUnitary A phase) = _
    exact (spectralSignUnitary_isSymmetric A phase).adjoint_eq
  rw [hstar, spectralSignUnitary, Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro mu _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro nu _
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  congr 1
  ring

/-- Distinct spectral blocks have cancelling signs when summed over all
Boolean phase assignments. -/
theorem sum_spectralSign_mul_eq_zero
    (A : L H) {mu nu : spectralEigenvalue A} (hmunu : mu ≠ nu) :
    ∑ phase : spectralEigenvalue A → Bool,
      spectralSign phase mu * spectralSign phase nu = 0 := by
  classical
  let toggle : (spectralEigenvalue A → Bool) →
      spectralEigenvalue A → Bool :=
    fun phase => Function.update phase mu (!(phase mu))
  change ∑ phase,
    spectralSign phase mu * spectralSign phase nu = 0
  apply Finset.sum_involution (s := Finset.univ)
      (fun phase _ => toggle phase)
  · intro phase _
    cases hmu : phase mu <;> cases hnu : phase nu <;>
      simp [toggle, spectralSign, hmu, hnu,
        Function.update_of_ne hmunu.symm]
  · intro phase _ _ heq
    have heqmu := congrFun heq mu
    cases hmu : phase mu <;> simp [toggle, hmu] at heqmu
  · intro phase _
    exact Finset.mem_univ _
  · intro phase _
    funext k
    by_cases hk : k = mu
    · subst k
      cases hmu : phase mu <;> simp [toggle, hmu]
    · simp [toggle, Function.update_of_ne hk]

/-- The diagonal sign coefficient sums to the number of Boolean phase
assignments. -/
theorem sum_spectralSign_mul_eq_card
    (A : L H) (mu : spectralEigenvalue A) :
    ∑ phase : spectralEigenvalue A → Bool,
      spectralSign phase mu * spectralSign phase mu =
        (Fintype.card (spectralEigenvalue A → Bool) : ℂ) := by
  classical
  simp only [spectralSign]
  conv_lhs =>
    enter [2, phase]
    rw [show (if phase mu = true then (-1 : ℂ) else 1) *
        (if phase mu = true then -1 else 1) = 1 by
      cases phase mu <;> simp]
  simp

/-- The unnormalised finite sum of all diagonal sign-unitary conjugations is
the cardinality multiple of spectral pinching. -/
theorem spectralPinching_mixedUnitary
    (A : L H) (hA : A.IsSymmetric) (X : L H) :
    (Fintype.card (spectralEigenvalue A → Bool) : ℂ) •
        (spectralPinchingChannel A hA).toFun X =
      ∑ phase : spectralEigenvalue A → Bool,
        spectralSignUnitary A phase * X * star (spectralSignUnitary A phase) := by
  classical
  rw [spectralPinchingChannel_apply]
  simp_rw [spectralSignUnitary_conjugation]
  rw [Finset.smul_sum, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro mu _
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single mu]
  · rw [← Finset.sum_smul, sum_spectralSign_mul_eq_card]
  · intro nu _ hnumu
    rw [← Finset.sum_smul, sum_spectralSign_mul_eq_zero A hnumu.symm,
      zero_smul]
  · intro hmu
    exact (hmu (Finset.mem_univ mu)).elim

/-- Spectral pinching is the normalized finite average of diagonal
sign-unitary conjugations. -/
theorem spectralPinching_mixedUnitary_average
    (A : L H) (hA : A.IsSymmetric) (X : L H) :
    (spectralPinchingChannel A hA).toFun X =
      ∑ phase : spectralEigenvalue A → Bool,
        (Fintype.card (spectralEigenvalue A → Bool) : ℂ)⁻¹ •
          (spectralSignUnitary A phase * X *
            star (spectralSignUnitary A phase)) := by
  classical
  have hcard : (Fintype.card (spectralEigenvalue A → Bool) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  calc
    (spectralPinchingChannel A hA).toFun X =
        (Fintype.card (spectralEigenvalue A → Bool) : ℂ)⁻¹ •
          ((Fintype.card (spectralEigenvalue A → Bool) : ℂ) •
            (spectralPinchingChannel A hA).toFun X) := by
      rw [smul_smul, inv_mul_cancel₀ hcard, one_smul]
    _ = (Fintype.card (spectralEigenvalue A → Bool) : ℂ)⁻¹ •
        ∑ phase : spectralEigenvalue A → Bool,
          spectralSignUnitary A phase * X *
            star (spectralSignUnitary A phase) := by
      rw [spectralPinching_mixedUnitary]
    _ = _ := by rw [Finset.smul_sum]

/-! ### Pinching inequality -/

/-- The sum of all ordered spectral-projector differences is twice the exact
pinching-inequality remainder. -/
theorem spectralProjector_pair_sum
    (A : L H) (hA : A.IsSymmetric) (X : L H) :
    ∑ mu : spectralEigenvalue A, ∑ nu : spectralEigenvalue A,
        (spectralProjector A mu - spectralProjector A nu) * X *
          (spectralProjector A mu - spectralProjector A nu) =
      2 • ((Fintype.card (spectralEigenvalue A) : ℂ) •
        (spectralPinchingChannel A hA).toFun X - X) := by
  classical
  have hexpand (mu nu : spectralEigenvalue A) :
      (spectralProjector A mu - spectralProjector A nu) * X *
          (spectralProjector A mu - spectralProjector A nu) =
        spectralProjector A mu * X * spectralProjector A mu -
          spectralProjector A mu * X * spectralProjector A nu -
          spectralProjector A nu * X * spectralProjector A mu +
          spectralProjector A nu * X * spectralProjector A nu := by
    noncomm_ring
  have hdiagLeft :
      (∑ mu : spectralEigenvalue A, ∑ _nu : spectralEigenvalue A,
          spectralProjector A mu * X * spectralProjector A mu) =
        (Fintype.card (spectralEigenvalue A) : ℂ) •
          ∑ mu : spectralEigenvalue A,
            spectralProjector A mu * X * spectralProjector A mu := by
    simp only [Finset.sum_const, Finset.card_univ]
    simp only [← Nat.cast_smul_eq_nsmul ℂ]
    rw [Finset.smul_sum]
  have hdiagRight :
      (∑ _mu : spectralEigenvalue A, ∑ nu : spectralEigenvalue A,
          spectralProjector A nu * X * spectralProjector A nu) =
        (Fintype.card (spectralEigenvalue A) : ℂ) •
          ∑ nu : spectralEigenvalue A,
            spectralProjector A nu * X * spectralProjector A nu := by
    rw [Finset.sum_comm]
    exact hdiagLeft
  have hcross :
      (∑ mu : spectralEigenvalue A, ∑ nu : spectralEigenvalue A,
          spectralProjector A mu * X * spectralProjector A nu) = X := by
    calc
      (∑ mu : spectralEigenvalue A, ∑ nu : spectralEigenvalue A,
          spectralProjector A mu * X * spectralProjector A nu) =
          ∑ mu : spectralEigenvalue A,
            (spectralProjector A mu * X) *
              ∑ nu : spectralEigenvalue A, spectralProjector A nu := by
        simp_rw [Finset.mul_sum]
      _ = ∑ mu : spectralEigenvalue A, spectralProjector A mu * X := by
        rw [spectralProjector_sum_eq_one A hA]
        simp
      _ = (∑ mu : spectralEigenvalue A, spectralProjector A mu) * X := by
        rw [Finset.sum_mul]
      _ = X := by rw [spectralProjector_sum_eq_one A hA, one_mul]
  have hcross' :
      (∑ mu : spectralEigenvalue A, ∑ nu : spectralEigenvalue A,
          spectralProjector A nu * X * spectralProjector A mu) = X := by
    rw [Finset.sum_comm]
    exact hcross
  simp_rw [hexpand, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hdiagLeft, hcross, hcross', hdiagRight,
    ← spectralPinchingChannel_apply A hA X]
  module

/-- Conjugating a non-negative operator by a difference of two spectral
projectors remains non-negative. -/
theorem spectralProjector_difference_conj_nonneg
    (A X : L H) (hX : 0 ≤ X) (mu nu : spectralEigenvalue A) :
    0 ≤ (spectralProjector A mu - spectralProjector A nu) * X *
      (spectralProjector A mu - spectralProjector A nu) := by
  apply (LinearMap.nonneg_iff_isPositive _).mpr
  have hS : (spectralProjector A mu -
      spectralProjector A nu).IsSymmetric :=
    (spectralProjector_isSymmetric A mu).sub
      (spectralProjector_isSymmetric A nu)
  have hconj := ((LinearMap.nonneg_iff_isPositive X).mp hX).conj_adjoint
    (spectralProjector A mu - spectralProjector A nu)
  simpa [hS.adjoint_eq] using hconj

/-- Positivity of twice an operator implies positivity of the operator. -/
theorem isPositive_of_two_nsmul
    {X : L H} (hX : (2 • X).IsPositive) : X.IsPositive := by
  constructor
  · intro x y
    have hsym := hX.1 x y
    simp only [two_nsmul, LinearMap.add_apply, inner_add_left,
      inner_add_right] at hsym
    linear_combination (1 / 2 : ℂ) * hsym
  · intro x
    have hquad := hX.2 x
    simp only [two_nsmul, LinearMap.add_apply, inner_add_left,
      map_add] at hquad
    linarith

/-- The pinching inequality with the exact number of distinct spectral
blocks, rather than the ambient Hilbert-space dimension. -/
theorem le_card_spectralPinching
    (A : L H) (hA : A.IsSymmetric) (X : L H) (hX : 0 ≤ X) :
    X ≤ (Fintype.card (spectralEigenvalue A) : ℂ) •
      (spectralPinchingChannel A hA).toFun X := by
  rw [← sub_nonneg]
  apply (LinearMap.nonneg_iff_isPositive _).mpr
  apply isPositive_of_two_nsmul
  apply (LinearMap.nonneg_iff_isPositive _).mp
  rw [← spectralProjector_pair_sum A hA X]
  apply Finset.sum_nonneg
  intro mu _
  apply Finset.sum_nonneg
  intro nu _
  exact spectralProjector_difference_conj_nonneg A X hX mu nu

/-! ## Hilbert--Schmidt self-adjointness and trace collapse -/

/-- Spectral pinching is self-adjoint for the Hilbert--Schmidt trace pairing. -/
theorem trace_mul_spectralPinching
    (sigma : L H) (hsigma : sigma.IsSymmetric) (A B : L H) :
    Tr (A * (spectralPinchingChannel sigma hsigma).toFun B) =
      Tr ((spectralPinchingChannel sigma hsigma).toFun A * B) := by
  rw [spectralPinchingChannel_apply, spectralPinchingChannel_apply,
    Finset.mul_sum, Finset.sum_mul, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro mu _
  calc
    Tr (A * (spectralProjector sigma mu * B * spectralProjector sigma mu)) =
        Tr ((spectralProjector sigma mu * A * spectralProjector sigma mu) * B) := by
      rw [show A * (spectralProjector sigma mu * B * spectralProjector sigma mu) =
          (A * spectralProjector sigma mu * B) * spectralProjector sigma mu by
        simp only [mul_assoc]]
      simpa only [mul_assoc] using
        (LinearMap.trace_mul_comm ℂ (spectralProjector sigma mu)
          (A * spectralProjector sigma mu * B)).symm
    _ = _ := rfl

/-- If `A` belongs to the fixed-point algebra of spectral pinching by
`sigma`, then pinching the other trace factor does not change the trace. -/
theorem trace_mul_eq_trace_mul_spectralPinching_of_fixed
    (sigma : L H) (hsigma : sigma.IsSymmetric) (A B : L H)
    (hA : (spectralPinchingChannel sigma hsigma).toFun A = A) :
    Tr (A * B) = Tr (A * (spectralPinchingChannel sigma hsigma).toFun B) := by
  rw [trace_mul_spectralPinching sigma hsigma A B, hA]

end

end QuantumChannel
