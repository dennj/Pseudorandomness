import Pseudorandomness.Foundations.MeasureCrypto
import Pseudorandomness.Applications.ControlTheoryBridge

/-!
  Stochastic Control Bridge (Measure-Crypto API)
  =============================================

  This file gives a control-theory-facing application of the measure-theoretic
  pseudorandomness layer in `Foundations/MeasureCrypto.lean`.

  Viewpoint: a (possibly noisy) system induces, for each horizon, a distribution on output traces.
  If the output-trace distributions for two states/parameters are computationally indistinguishable
  for a class `D` of distinguishers, then any `D`-bounded estimator cannot have a non-negligible
  success-probability gap between the two worlds.

  This is the same meta-principle as “learning as distinguishing”, but here the “examples” are
  output traces of a dynamical system.
-/

namespace Pseudorandomness

open Filter

namespace StochasticControl

open MeasureTheory
open CryptoMeasure
open LearningGame

/-! ## Deterministic linear systems as trace ensembles

As a minimal, fully provable application (no axioms, no Gaussian measures),
we interpret the deterministic output sequence of `ControlTheory.LinearSystem` as a
`ProbabilityMeasure` via a Dirac distribution.

This already yields a clean statement:
if two initial states produce the same output trace, then *no* distinguisher (hence no estimator)
can tell them apart from trace data.
-/

variable {𝕜 : Type*} [Field 𝕜] [MeasurableSpace 𝕜]
variable {n m : ℕ}
variable (sys : ControlTheory.LinearSystem 𝕜 n m)

abbrev Trace : Type _ :=
  Fin n → (Fin m → 𝕜)

noncomputable def traceMeasure (x₀ : Fin n → 𝕜) : ProbabilityMeasure (Trace (𝕜 := 𝕜) (n := n) (m := m)) :=
  ⟨Measure.dirac (sys.outputSequence x₀ n), Measure.dirac.isProbabilityMeasure⟩

/-- Package the deterministic trace as an `Ensemble` (constant in the security parameter). -/
noncomputable def traceEnsemble (x₀ : Fin n → 𝕜) : Ensemble (fun _k : ℕ => Trace (𝕜 := 𝕜) (n := n) (m := m)) :=
  fun _k => traceMeasure (sys := sys) x₀

theorem traceEnsemble_eq_of_outputSequence_eq {x₀ x₀' : Fin n → 𝕜}
    (h : sys.outputSequence x₀ n = sys.outputSequence x₀' n) :
    traceEnsemble (sys := sys) x₀ = traceEnsemble (sys := sys) x₀' := by
  funext k
  apply Subtype.ext
  -- extensionality on the underlying `Measure` of the `ProbabilityMeasure`
  simp [traceEnsemble, traceMeasure, h]

/-! ## Indistinguishability ⇒ no-estimation advantage (trace data)

We phrase this using the generic `LearningGame` API:
- an `Example` is a trace;
- a learner/estimator takes `m(n)` i.i.d. traces and outputs a hypothesis;
- a `SuccessPred` turns a hypothesis into a `Bool` (e.g. “within tolerance”).
-/

theorem negligible_success_gap_of_equal_traces
    {mSamples : ℕ → ℕ} {Hyp : ℕ → Type*}
    {D : Set (Distinguisher (Samples (fun _k : ℕ => Trace (𝕜 := 𝕜) (n := n) (m := m)) mSamples))}
    (L : Learner (fun _k : ℕ => Trace (𝕜 := 𝕜) (n := n) (m := m)) Hyp mSamples)
    (good : SuccessPred Hyp)
    {x₀ x₀' : Fin n → 𝕜}
    (hTrace : sys.outputSequence x₀ n = sys.outputSequence x₀' n)
    (hmem : learnerDistinguisher (L := L) (good := good) ∈ D) :
    Negligible (fun k =>
      |successProb (X := traceEnsemble (sys := sys) x₀) (m := mSamples) L good k -
        successProb (X := traceEnsemble (sys := sys) x₀') (m := mSamples) L good k|) := by
  have hEq : traceEnsemble (sys := sys) x₀ = traceEnsemble (sys := sys) x₀' :=
    traceEnsemble_eq_of_outputSequence_eq (sys := sys) hTrace
  have hInd :
      Indistinguishable D (iidSamplesEnsemble (traceEnsemble (sys := sys) x₀) mSamples)
        (iidSamplesEnsemble (traceEnsemble (sys := sys) x₀') mSamples) := by
    -- rewrite to reflexivity
    simpa [hEq] using
      (Indistinguishable.refl (D := D) (X := iidSamplesEnsemble (traceEnsemble (sys := sys) x₀) mSamples))
  exact
    LearningGame.negligible_abs_successProb_sub_of_indistinguishable
      (X := traceEnsemble (sys := sys) x₀)
      (Y := traceEnsemble (sys := sys) x₀')
      (m := mSamples) (D := D) (L := L) (good := good) hInd hmem

section NoMeasure

variable {𝕜 : Type*} [Field 𝕜]
variable {n m : ℕ}
variable (sys : ControlTheory.LinearSystem 𝕜 n m)

theorem exists_equal_trace_of_not_observable
    (hNotObs : ¬sys.IsObservable) :
    ∃ x₀ x₀' : Fin n → 𝕜, x₀ ≠ x₀' ∧ sys.outputSequence x₀ n = sys.outputSequence x₀' n := by
  classical
  -- Unfold the semantic definition of observability and negate it.
  have : ∃ x₀ x₀' : Fin n → 𝕜,
      (∀ t : Fin n, sys.outputAt x₀ t = sys.outputAt x₀' t) ∧ x₀ ≠ x₀' := by
    simpa [ControlTheory.LinearSystem.IsObservable] using hNotObs
  rcases this with ⟨x₀, x₀', hEqOut, hNe⟩
  refine ⟨x₀, x₀', hNe, ?_⟩
  funext t
  exact hEqOut t

end NoMeasure

end StochasticControl

end Pseudorandomness
