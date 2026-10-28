import Quantum.TraceInequality.Loewner.Statement
import Quantum.TraceInequality.Loewner.Koranyi.SupportElimination
import Quantum.TraceInequality.Loewner.Koranyi.PickLimit
import Quantum.TraceInequality.Loewner.Koranyi.CayleyPushforward
import Quantum.TraceInequality.Loewner.Koranyi.OneSubMulKernel
import Quantum.TraceInequality.Loewner.Koranyi.SignedPoints

namespace Quantum.TraceInequality

open MeasureTheory Set Filter

open scoped Topology UpperHalfPlane

noncomputable section

namespace Loewner

/-- Condition 1: nonnegativity of the imaginary part of the per-n Stieltjes transform (raw only). -/
def StieltjesImNonnegAll (μn : ℕ → Measure ℝ) : Prop :=
  ∀ n : ℕ, ∀ z : ℍ, 0 ≤ (stieltjes (μn n) z).im

/-- Condition 2: uniform convergence on `KmHT m` of the outside Stieltjes-difference integral. -/
def OutsideStieltjesDiffTendstoUniformlyOnKm
    (μn : ℕ → Measure ℝ) (φ : ℕ → ℕ) (F : ℍ → ℂ) : Prop :=
  ∀ m : ℕ,
    TendstoUniformly
        (fun n (z : KmHT m) =>
          ∫ y, ((1 / (y : ℂ)) - (1 / ((y : ℂ) - (z.1 : ℂ)⁻¹)))
            ∂((μn (φ n)).restrict (Set.Icc (-1 : ℝ) 1)ᶜ))
        (fun z => F z.1) atTop

/-- Condition 3: pointwise convergence of the support-eliminated Stieltjes transform. -/
def SupportElimStieltjesTendsto
    (μn : ℕ → Measure ℝ) (φ : ℕ → ℕ) (F : ℍ → ℂ) : Prop :=
  ∀ z : ℍ,
    Tendsto
      (fun n => stieltjes (supportElimMeasure (μn (φ n))) z)
      atTop (𝓝 (F z))

/-- Condition 4: pointwise convergence of the outside Stieltjes-difference integral. -/
def OutsideStieltjesDiffTendsto
    (μn : ℕ → Measure ℝ) (φ : ℕ → ℕ) (F : ℍ → ℂ) : Prop :=
  ∀ z : ℍ,
    Tendsto
        (fun n =>
          ∫ y, ((1 / (y : ℂ)) - (1 / ((y : ℂ) - (z : ℂ)⁻¹)))
            ∂((μn (φ n)).restrict (Set.Icc (-1 : ℝ) 1)ᶜ))
        atTop (𝓝 (F z))

/-- Condition 5: finite-point evaluation identity at reciprocal points. `ι = id` gives the per-n
version, `ι = φ` the subsequence version. -/
def EvalInvOn (f : ℝ → ℝ) (y : ∀ n : ℕ, Fin (n + 1) → ℝ)
    (μn : ℕ → Measure ℝ) (ι : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, ∀ i : Fin (ι n + 1), i ≠ 0 →
    (f (y (ι n) i) : ℂ) =
      (f 0 : ℂ) -
        ∫ t, (1 / ((t : ℂ) - (1 / (y (ι n) i : ℂ)))) ∂(μn (ι n))

/-- Condition 6: finite-point evaluation identity in the `1 - y * t` kernel form. `ι = id` gives the
per-n version, `ι = φ` the subsequence version. -/
def OneSubMulEvalOn (f : ℝ → ℝ) (y : ∀ n : ℕ, Fin (n + 1) → ℝ)
    (μn : ℕ → Measure ℝ) (ι : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, ∀ i : Fin (ι n + 1), i ≠ 0 →
    (f (y (ι n) i) : ℂ) =
      (f 0 : ℂ) +
        (y (ι n) i : ℂ) *
          ∫ t, (1 / (1 - (y (ι n) i : ℂ) * (t : ℂ))) ∂(μn (ι n))

/-- Condition 7: integrability of `oneSubMulKernelC`. It does not depend on the point family (only
on `μn ∘ ι`). -/
def OneSubMulKernelIntegrableOn (μn : ℕ → Measure ℝ) (ι : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, ∀ x : ℝ,
    Integrable (fun t : ℝ => oneSubMulKernelC x t) (μn (ι n))

/-- Condition 8: pointwise limit of the outside `1 - y*t` kernel integral difference. -/
def OneSubMulKernelDiffTendsto
    (μn : ℕ → Measure ℝ) (φ : ℕ → ℕ) (F : ℍ → ℂ) : Prop :=
  ∀ z w : ℍ,
    Tendsto
        (fun n =>
          (∫ t, (z : ℂ) * (1 / (1 - (z : ℂ) * (t : ℂ)))
              ∂((μn (φ n)).restrict (Set.Icc (-1 : ℝ) 1)ᶜ)) -
            ∫ t, (w : ℂ) * (1 / (1 - (w : ℂ) * (t : ℂ)))
              ∂((μn (φ n)).restrict (Set.Icc (-1 : ℝ) 1)ᶜ))
        atTop (𝓝 (F z - F w))

/-- Condition 9: uniform limit on `KmHT m`, for each anchor `w`, of the outside `1 - y*t` kernel
integral difference. -/
def OneSubMulKernelDiffTendstoUniformlyOnKm
    (μn : ℕ → Measure ℝ) (φ : ℕ → ℕ) (F : ℍ → ℂ) : Prop :=
  ∀ w : ℍ,
    ∀ m : ℕ,
      TendstoUniformly
          (fun n (z : KmHT m) =>
            (∫ t, (z.1 : ℂ) * (1 / (1 - (z.1 : ℂ) * (t : ℂ)))
                ∂((μn (φ n)).restrict (Set.Icc (-1 : ℝ) 1)ᶜ)) -
              ∫ t, (w : ℂ) * (1 / (1 - (w : ℂ) * (t : ℂ)))
                ∂((μn (φ n)).restrict (Set.Icc (-1 : ℝ) 1)ᶜ))
          (fun z => F z.1 - F w) atTop

/-- Condition 10: monotonicity of `ratioFunctional ν ∘ cayley` on `(-1, 1)`. -/
def RatioFunctionalCayleyMonotoneOn (ν : FiniteMeasure ENNReal) : Prop :=
  MonotoneOn
    (fun x : ℝ => (ratioFunctional ν (Real.toNNReal (cayley x)) : ENNReal))
    (Set.Ioo (-1 : ℝ) 1)

/-- Condition 11: `1 - y*t` integral representation of the zero-axis Löwner kernel (a separate
condition used only for the signed family). -/
def ZeroAxisOneSubMulEvalOn (f : ℝ → ℝ) (y : ∀ n : ℕ, Fin (n + 1) → ℝ)
    (μn : ℕ → Measure ℝ) (ι : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, ∀ i : Fin (ι n + 1), i ≠ 0 →
    (loewnerKernel f (y (ι n) i) 0 : ℂ) =
      ∫ t, (1 / (1 - (y (ι n) i : ℂ) * (t : ℂ))) ∂(μn (ι n))

open scoped ComplexOrder MatrixOrder

/-- Internal Chapter 20/27 package reused from the current Koranyi/support-elimination backbone. -/
structure StrictApproxPackage (f : ℝ → ℝ) where
  μn : ℕ → Measure ℝ
  M0 : ENNReal
  hM0 : M0 < ⊤
  hμle : ∀ n : ℕ, μn n Set.univ ≤ M0
  hMass :
    ∀ n : ℕ, μn n Set.univ = ENNReal.ofReal (loewnerKernel f 0 0)
  φ : ℕ → ℕ
  hφ : StrictMono φ
  F : ℍ → ℂ
  ν : FiniteMeasure ENNReal
  hStieltjes :
    ∀ m : ℕ,
      TendstoUniformly
        (fun n (z : KmHT m) =>
          stieltjes (supportElimMeasure (μn (φ n))) z.1)
        (fun z => F z.1) atTop
  hPick :
    ∀ z : ℍ, 0 ≤ (F z).im
  hCayleyWeak :
    Tendsto
      (fun n =>
        cayleyPushforward
          (⟨supportElimMeasure (μn (φ n)),
              ⟨lt_of_le_of_lt
                  ((supportElimMeasure_univ_le (μ := μn (φ n))).trans (hμle (φ n)))
                  hM0⟩⟩ :
            FiniteMeasure ℝ))
      atTop (𝓝 ν)
  hKoranyi :
    ∀ x : ℝ,
      x ∈ Set.Ioo (-1 : ℝ) 1 →
        Tendsto
          (fun n =>
            ∫⁻ t, (Real.toNNReal (koranyiKernel x t) : ENNReal)
              ∂(supportElimMeasure (μn (φ n))))
          atTop
          (𝓝 ((ratioFunctional ν (Real.toNNReal (cayley x))) : ENNReal))

/-- Raw base: measure sequence + uniform mass bound + mass identity + per-n Stieltjes nonnegativity
(G01). -/
structure RawMeasureSeqPackage (f : ℝ → ℝ) where
  μn : ℕ → Measure ℝ
  M0 : ENNReal
  hM0 : M0 < ⊤
  hμle : ∀ n : ℕ, μn n Set.univ ≤ M0
  hMass :
    ∀ n : ℕ, μn n Set.univ = ENNReal.ofReal (loewnerKernel f 0 0)
  hStieltjesNonneg : StieltjesImNonnegAll μn

/-- Raw + per-n evalInv identity (G03). -/
structure RawEvalInvPackage (f : ℝ → ℝ) (y : ∀ n : ℕ, Fin (n + 1) → ℝ)
    extends RawMeasureSeqPackage f where
  hEvalInv : EvalInvOn f y μn id

/-- Raw evalInv + per-n kernel integrability (G02). -/
structure RawEvalInvKernelIntegrablePackage (f : ℝ → ℝ) (y : ∀ n : ℕ, Fin (n + 1) → ℝ)
    extends RawEvalInvPackage f y where
  hKernelIntegrable : OneSubMulKernelIntegrableOn μn id

/-- Raw + per-n oneSubMul identity (G05). -/
structure RawOneSubMulPackage (f : ℝ → ℝ) (y : ∀ n : ℕ, Fin (n + 1) → ℝ)
    extends RawMeasureSeqPackage f where
  hOneSubMul : OneSubMulEvalOn f y μn id

/-- Raw oneSubMul + per-n kernel integrability (G04). -/
structure RawOneSubMulKernelIntegrablePackage (f : ℝ → ℝ) (y : ∀ n : ℕ, Fin (n + 1) → ℝ)
    extends RawOneSubMulPackage f y where
  hKernelIntegrable : OneSubMulKernelIntegrableOn μn id

/-- Name in the v3 taxonomy. The 13 fields of the S short form coincide exactly with the existing
StrictApproxPackage, so no separate structure is introduced (fields are not restated). -/
abbrev KoranyiLimitPackage (f : ℝ → ℝ) : Type := StrictApproxPackage f

/-- S short form + monotonicity of the ratio functional (G19/G20). -/
structure KoranyiLimitMonotonePackage (f : ℝ → ℝ) extends StrictApproxPackage f where
  hMonotone : RatioFunctionalCayleyMonotoneOn ν

/-- Full ∧8 basic form: the 13 S fields + uniform convergence of the outside integral, pointwise
convergence of the Stieltjes transform, and pointwise convergence of the outside integral
(G06/G07). -/
structure StrictApproxFullPackage (f : ℝ → ℝ) extends StrictApproxPackage f where
  hOutsideUniform : OutsideStieltjesDiffTendstoUniformlyOnKm μn φ F
  hStieltjesTendsto : SupportElimStieltjesTendsto μn φ F
  hOutsideTendsto : OutsideStieltjesDiffTendsto μn φ F

/-- Full + per-n evalInv (G10; G13 is `y := canonicalPoints`). -/
structure FullEvalInvPackage (f : ℝ → ℝ) (y : ∀ n : ℕ, Fin (n + 1) → ℝ)
    extends StrictApproxFullPackage f where
  hEvalInv : EvalInvOn f y μn id

/-- Full + subsequence evalInv (G14, `y := canonicalPoints`). -/
structure FullEvalInvSubseqPackage (f : ℝ → ℝ) (y : ∀ n : ℕ, Fin (n + 1) → ℝ)
    extends StrictApproxFullPackage f where
  hEvalInvSubseq : EvalInvOn f y μn φ

/-- Full + per-n oneSubMul (G11; G15 is `y := canonicalPoints`). -/
structure FullOneSubMulPackage (f : ℝ → ℝ) (y : ∀ n : ℕ, Fin (n + 1) → ℝ)
    extends StrictApproxFullPackage f where
  hOneSubMul : OneSubMulEvalOn f y μn id

/-- Full + subsequence oneSubMul (G16, `y := canonicalPoints`). -/
structure FullOneSubMulSubseqPackage (f : ℝ → ℝ) (y : ∀ n : ℕ, Fin (n + 1) → ℝ)
    extends StrictApproxFullPackage f where
  hOneSubMulSubseq : OneSubMulEvalOn f y μn φ

/-- Full oneSubMul (per-n) + subsequence kernel integrability (G12).
The asymmetry of the existing code (integrable uses `μn (φ n)`, eval uses `μn n`) is kept as is. -/
structure FullOneSubMulKernelIntegrablePackage (f : ℝ → ℝ)
    (y : ∀ n : ℕ, Fin (n + 1) → ℝ)
    extends FullOneSubMulPackage f y where
  hKernelIntegrableSubseq : OneSubMulKernelIntegrableOn μn φ

/-- Full subsequence oneSubMul + pointwise kernel-difference limit (G17, `y := canonicalPoints`). -/
structure FullOneSubMulSubseqKernelLimitPackage (f : ℝ → ℝ)
    (y : ∀ n : ℕ, Fin (n + 1) → ℝ)
    extends FullOneSubMulSubseqPackage f y where
  hKernelDiffTendsto : OneSubMulKernelDiffTendsto μn φ F

/-- Full subsequence oneSubMul + pointwise kernel-difference limit + uniform limit (G18,
`y := canonicalPoints`). -/
structure FullOneSubMulSubseqUniformKernelLimitPackage (f : ℝ → ℝ)
    (y : ∀ n : ℕ, Fin (n + 1) → ℝ)
    extends FullOneSubMulSubseqKernelLimitPackage f y where
  hKernelDiffUniform : OneSubMulKernelDiffTendstoUniformlyOnKm μn φ F

/-- Full + subsequence kernel integrability + signedPoints zero-axis identity (G21). -/
structure FullSignedZeroAxisKernelIntegrablePackage (f : ℝ → ℝ)
    extends StrictApproxFullPackage f where
  hKernelIntegrableSubseq : OneSubMulKernelIntegrableOn μn φ
  hSignedZeroAxis : ZeroAxisOneSubMulEvalOn f signedPoints μn φ

end Loewner

end

end TraceInequality
end Quantum
