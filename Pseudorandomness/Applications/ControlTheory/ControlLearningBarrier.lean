import Pseudorandomness.Core.LearningBarrier
import Pseudorandomness.Applications.ControlTheory.StochasticControlBridge

/-!
  Control Learning Barrier
  =======================

  This file instantiates the `LearningBarrier` theorem in the control-theory setting:

  - Examples are output traces of a system.
  - Learners are estimators operating on i.i.d. trace samples.
  - If two initial states/parameters induce computationally indistinguishable trace ensembles
    (for a distinguisher class `D`), then every `D`-bounded estimator has only negligible
    success-probability gap between those two worlds.

  This is the direct analog of instantiating `observer_barrier` with a concrete observer class.
-/

namespace Pseudorandomness

open Filter

namespace ControlLearningBarrier

open MeasureTheory
open CryptoMeasure
open LearningGame
open LearningBarrier
open StochasticControl

variable {𝕜 : Type*} [Field 𝕜] [MeasurableSpace 𝕜]
variable {n m : ℕ}
variable (sys : ControlTheory.LinearSystem 𝕜 n m)

abbrev TraceExample : ℕ → Type _ :=
  fun _k => StochasticControl.Trace (𝕜 := 𝕜) (n := n) (m := m)

noncomputable instance : ∀ k, MeasurableSpace (TraceExample (𝕜 := 𝕜) (n := n) (m := m) k) :=
  fun _k => inferInstance

variable {mSamples : ℕ → ℕ}
variable {Hyp : ℕ → Type*}

abbrev Technique :=
  LearningBarrier.LearningTechnique (Example := TraceExample (𝕜 := 𝕜) (n := n) (m := m)) (Hyp := Hyp)
    (m := mSamples)

/--
If the trace ensembles induced by two states are indistinguishable for the technique’s `D`,
then every estimator in the technique has only negligible success-gap between the two states.
-/
theorem barrier_of_indistinguishable_traces (tech : Technique (𝕜 := 𝕜) (n := n) (m := m) (mSamples := mSamples) (Hyp := Hyp))
    {x₀ x₀' : Fin n → 𝕜}
    (hInd :
      Indistinguishable tech.D
        (iidSamplesEnsemble (StochasticControl.traceEnsemble (sys := sys) x₀) mSamples)
        (iidSamplesEnsemble (StochasticControl.traceEnsemble (sys := sys) x₀') mSamples)) :
    ∀ L ∈ tech.learners,
      Negligible (fun k =>
        |successProb (X := StochasticControl.traceEnsemble (sys := sys) x₀) (m := mSamples) L tech.good k -
          successProb (X := StochasticControl.traceEnsemble (sys := sys) x₀') (m := mSamples) L tech.good k|) := by
  -- direct instantiation of the generic barrier theorem
  simpa [Technique, TraceExample] using
    (LearningBarrier.learning_barrier (tech := tech)
      (X := StochasticControl.traceEnsemble (sys := sys) x₀)
      (Y := StochasticControl.traceEnsemble (sys := sys) x₀') hInd)

/--
Deterministic corollary: if two states produce the same output trace, then the ensembles are equal,
hence indistinguishable; therefore any bounded estimator has negligible success-gap.
-/
theorem barrier_of_equal_traces (tech : Technique (𝕜 := 𝕜) (n := n) (m := m) (mSamples := mSamples) (Hyp := Hyp))
    {x₀ x₀' : Fin n → 𝕜}
    (hTrace : sys.outputSequence x₀ n = sys.outputSequence x₀' n) :
    ∀ L ∈ tech.learners,
      Negligible (fun k =>
        |successProb (X := StochasticControl.traceEnsemble (sys := sys) x₀) (m := mSamples) L tech.good k -
          successProb (X := StochasticControl.traceEnsemble (sys := sys) x₀') (m := mSamples) L tech.good k|) := by
  have hEq : StochasticControl.traceEnsemble (sys := sys) x₀ = StochasticControl.traceEnsemble (sys := sys) x₀' :=
    StochasticControl.traceEnsemble_eq_of_outputSequence_eq (sys := sys) hTrace
  have hInd :
      Indistinguishable tech.D
        (iidSamplesEnsemble (StochasticControl.traceEnsemble (sys := sys) x₀) mSamples)
        (iidSamplesEnsemble (StochasticControl.traceEnsemble (sys := sys) x₀') mSamples) := by
    simpa [hEq] using
      (Indistinguishable.refl (D := tech.D)
        (X := iidSamplesEnsemble (StochasticControl.traceEnsemble (sys := sys) x₀) mSamples))
  exact barrier_of_indistinguishable_traces (sys := sys) (tech := tech) hInd

/--
Non-observability corollary (deterministic): if `sys` is not observable, there exist distinct states
with identical traces, hence the barrier applies to that pair.
-/
theorem exists_pair_barrier_of_not_observable (tech : Technique (𝕜 := 𝕜) (n := n) (m := m) (mSamples := mSamples) (Hyp := Hyp))
    (hNotObs : ¬sys.IsObservable) :
    ∃ x₀ x₀' : Fin n → 𝕜, x₀ ≠ x₀' ∧
      (∀ L ∈ tech.learners,
        Negligible (fun k =>
          |successProb (X := StochasticControl.traceEnsemble (sys := sys) x₀) (m := mSamples) L tech.good k -
            successProb (X := StochasticControl.traceEnsemble (sys := sys) x₀') (m := mSamples) L tech.good k|)) := by
  classical
  -- the witness pair comes from the semantic control bridge
  obtain ⟨x₀, x₀', hNe, hTrace⟩ :=
    StochasticControl.exists_equal_trace_of_not_observable (sys := sys) hNotObs
  refine ⟨x₀, x₀', hNe, ?_⟩
  exact barrier_of_equal_traces (sys := sys) (tech := tech) hTrace

end ControlLearningBarrier

end Pseudorandomness
