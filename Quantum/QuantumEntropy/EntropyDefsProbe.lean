import Quantum.QuantumEntropy.UmegakiDPI.AlphaOneCore
import Quantum.QuantumEntropy.VonNeumann.Consequences
import Mathlib.Util.AssertNoSorry
import Quantum.QuantumEntropy.Common.PositiveDefiniteCertificatesGeneralizedStein
import Quantum.QuantumEntropy.Common.TensorDensitySupport.GSLCoreGeneralizedStein
import Quantum.QuantumEntropy.Common.TraceReGeneralizedStein
import Quantum.QuantumEntropy.SandwichedRenyi.Internal.BridgeCertificates
import Quantum.QuantumEntropy.SandwichedRenyiRelativeEntropy
import Quantum.QuantumEntropy.UmegakiDPI.ViaPetz.FromRenyi.GSLCore
import Quantum.QuantumMechanics.Channel.ChoiKrausGeneralizedStein
import Quantum.QuantumMechanics.QuantumChannel
import Quantum.TraceInequality.GeneralizedPerspectiveFunctionRetained
import Quantum.TraceInequality.HansenPedersen.LownerHeinzTheorem
import Quantum.TraceInequality.LiebTrace.MonotonicityRetained
import Quantum.TraceInequality.LownerHeinz.ReciprocalRetained

/-!
# Direct entropy-definition regression probe

This file makes the root build fail if either entropy definition returns to the old
continuous-linear-map round trip, if either proposition-level bridge changes, or if the
frozen public theorem set acquires nonstandard axioms or a `sorry`.
-/

open QuantumState

universe u

variable {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]

example (ρ : L ℋ) :
    VonNeumann.vonNeumannEntropy ρ = -(Tr (ρ * CFC.log ρ)).re :=
  rfl

example (ρ σ : L ℋ) :
    SandwichedRenyiRelativeEntropy.umegakiNorm ρ σ =
      (Tr (ρ * (CFC.log ρ - CFC.log σ))).re / (Tr ρ).re :=
  rfl

example (ρ : L ℋ) :
    VonNeumann.vonNeumannEntropy ρ =
      -(Tr ((ρ.toContinuousLinearMap *
        CFC.log ρ.toContinuousLinearMap : B ℋ) : L ℋ)).re :=
  VonNeumann.vonNeumannEntropy_def ρ

example (ρ σ : L ℋ) :
    SandwichedRenyiRelativeEntropy.umegakiNorm ρ σ =
      (Tr (((ρ.toContinuousLinearMap *
        (CFC.log ρ.toContinuousLinearMap - CFC.log σ.toContinuousLinearMap) : B ℋ) :
          L ℋ))).re / (Tr ρ).re :=
  SandwichedRenyiRelativeEntropy.umegakiNorm_eq_toContinuousLinearMap ρ σ

open Lean in
run_meta
  let decls := #[
    ``VonNeumann.vonNeumannEntropy,
    ``SandwichedRenyiRelativeEntropy.umegakiNorm
  ]
  for declName in decls do
    let some info@(.defnInfo _) := (← getEnv).find? declName
      | throwError "expected definition {declName} is unavailable as defnInfo"
    let some value := info.value?
      | throwError "expected stored value for definition {declName}"
    if (value.find? fun
        | .const name _ => name == ``LinearMap.toContinuousLinearMap
        | _ => false).isSome then
      throwError "{declName} stored value contains LinearMap.toContinuousLinearMap"
    logInfo m!"value guard PASS {declName}: LinearMap.toContinuousLinearMap absent"

open Lean in
run_meta
  let expected := [``propext, ``Classical.choice, ``Quot.sound]
  let decls := #[
    ``CFCTransport.cfc_log_toCLM,
    ``CFCTransport.cfc_rpow_toCLM,
    ``VonNeumann.vonNeumannEntropy_def,
    ``SandwichedRenyiRelativeEntropy.umegakiNorm_eq_toContinuousLinearMap,
    ``VonNeumann.strongSubadditivity,
    ``VonNeumann.strongSubadditivity_of_state,
    ``VonNeumann.umegakiNorm_nonneg_of_state,
    ``VonNeumann.subadditivity,
    ``VonNeumann.mutualInformation_nonneg,
    ``VonNeumann.conditionalEntropySubadditivity,
    ``VonNeumann.subadditivity_of_state,
    ``VonNeumann.mutualInformation_nonneg_of_state,
    ``VonNeumann.conditionalEntropySubadditivity_of_state,
    ``SandwichedRenyiRelativeEntropy.umegakiNorm_monotone_pd,
    ``UmegakiDPI.monotoneNormOnNonNeg,
    ``UmegakiDPI.monotoneOnNonNeg
  ]
  for declName in decls do
    let axioms ← collectAxioms declName
    if axioms.contains ``sorryAx then
      throwError "axiom guard failed for {declName}: sorryAx present"
    for axiomName in expected do
      unless axioms.contains axiomName do
        throwError "axiom guard failed for {declName}: missing {axiomName}"
    for axiomName in axioms.toList do
      unless expected.contains axiomName do
        throwError "axiom guard failed for {declName}: unexpected {axiomName}"
    logInfo m!"axiom guard PASS {declName}: [propext, Classical.choice, Quot.sound]"
