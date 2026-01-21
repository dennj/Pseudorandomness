import Pseudorandomness.Foundations.MeasureCrypto

/-!
  Learning Barrier and Magnification (Domain-Agnostic)
  ====================================================

  This file packages the generic "learning as distinguishing" framework:

  ## Learning Barrier (Forward Direction)

  - A learner induces a distinguisher via `LearningGame.learnerDistinguisher`.
  - If two sample ensembles are computationally indistinguishable for a distinguisher class `D`,
    then any learner whose induced distinguisher lies in `D` can only have a negligible
    success-probability gap between the two worlds.

  This is the learning/estimation analog of instantiating `observer_barrier` with a bounded
  observer class, but it lives in the measure-theoretic (distribution) layer.

  ## Magnification (Converse Direction)

  In many places in complexity/learning, the pipeline is:

  1. A learner achieves a nontrivial advantage on a task (often very weak).
  2. Therefore we can build a distinguisher that *breaks* an indistinguishability claim.
  3. Any downstream consequence of breaking that indistinguishability can then be derived.

  This file formalizes (1)→(2) and packages (2)→(3) as a compositional lemma.

  No axioms are introduced: "consequences of breaking indistinguishability" are taken as explicit
  hypotheses in theorems, so later instantiations can plug in external reductions/results.

  ## Contrastive Learning Application

  We also package a modern ML/time-series pattern:

  - A *positive pair* distribution `J` on `(x, x')` (e.g. `x'` is an augmentation of `x`,
    or a temporally adjacent observation).
  - A *negative pair* distribution given by the product of marginals of `J`
    (a standard "shuffle negatives" baseline).

  A contrastive learner that achieves a non-negligible advantage between positives and negatives
  therefore yields a distinguisher that breaks indistinguishability.

  The results are intentionally domain-agnostic: they do not assume any specific architecture
  (neural networks, kernels, etc.), only the abstract `LearningTechnique` interface.
-/

namespace Pseudorandomness

open Filter
open MeasureTheory
open CryptoMeasure
open LearningGame

namespace LearningBarrier

universe u v

variable {Example : ℕ → Type u} {Hyp : ℕ → Type v}
variable [∀ n, MeasurableSpace (Example n)]
variable {m : ℕ → ℕ}

/-! ## Learning Technique Structure -/

/-- A "learning technique" is a class of learners with a success predicate, bounded by `D`. -/
structure LearningTechnique where
  learners : Set (Learner Example Hyp m)
  good : SuccessPred Hyp
  D : Set (Distinguisher (Samples Example m))
  bounded : ∀ L ∈ learners, learnerDistinguisher (L := L) (good := good) ∈ D

theorem Negligible.tendsto_abs_zero {f : ℕ → ℝ} (hf : CryptoMeasure.Negligible f) :
    Tendsto (fun n => |f n|) atTop (nhds 0) := by
  simpa using (hf 0)

/-! ## Learning Barrier (Forward Direction) -/

/--
**Learning barrier (generic)**: if two `m(n)`-sample ensembles are indistinguishable for `tech.D`,
then every learner in `tech.learners` has only a negligible success-probability gap.
-/
theorem learning_barrier (tech : LearningTechnique (Example := Example) (Hyp := Hyp) (m := m))
    (X Y : Ensemble Example)
    (hInd : Indistinguishable tech.D (iidSamplesEnsemble X m) (iidSamplesEnsemble Y m)) :
    ∀ L ∈ tech.learners,
      CryptoMeasure.Negligible (fun n =>
        |successProb (X := X) (m := m) L tech.good n -
          successProb (X := Y) (m := m) L tech.good n|) := by
  intro L hL
  have hmem : learnerDistinguisher (L := L) (good := tech.good) ∈ tech.D :=
    tech.bounded L hL
  simpa using
    (LearningGame.negligible_abs_successProb_sub_of_indistinguishable
      (X := X) (Y := Y) (m := m) (D := tech.D) (L := L) (good := tech.good) hInd hmem)

/--
Consequence in "tends to zero" form: the success-gap tends to `0` for each learner in the class.
-/
theorem learning_barrier_tendsto (tech : LearningTechnique (Example := Example) (Hyp := Hyp) (m := m))
    (X Y : Ensemble Example)
    (hInd : Indistinguishable tech.D (iidSamplesEnsemble X m) (iidSamplesEnsemble Y m)) :
    ∀ L ∈ tech.learners,
      Tendsto (fun n =>
        |successProb (X := X) (m := m) L tech.good n -
          successProb (X := Y) (m := m) L tech.good n|) atTop (nhds 0) := by
  intro L hL
  have hNeg :=
    learning_barrier (tech := tech) (X := X) (Y := Y) hInd L hL
  have hT : Tendsto (fun n =>
        |(fun n =>
            |successProb (X := X) (m := m) L tech.good n -
              successProb (X := Y) (m := m) L tech.good n|) n|) atTop (nhds 0) :=
    Negligible.tendsto_abs_zero (f := fun n =>
      |successProb (X := X) (m := m) L tech.good n -
        successProb (X := Y) (m := m) L tech.good n|) hNeg
  simpa [abs_abs] using hT

/-! ## Magnification (Converse Direction) -/

/-- A "break" of indistinguishability: some distinguisher in `D` has non-negligible advantage. -/
def Breaks (D : Set (Distinguisher (Samples Example m)))
    (X Y : Ensemble (Samples Example m)) : Prop :=
  ∃ d ∈ D, ¬Negligible (advantageEnsemble d X Y)

/--
If a learner in a `LearningTechnique` has non-negligible success-gap between `X` and `Y`,
then the technique's distinguisher class `D` breaks indistinguishability of the sample ensembles.
-/
theorem breaks_of_nonNegligible_successGap
    (tech : LearningTechnique (Example := Example) (Hyp := Hyp) (m := m))
    (X Y : Ensemble Example)
    {L : Learner Example Hyp m} (hL : L ∈ tech.learners)
    (hGap : ¬Negligible (fun n =>
      |successProb (X := X) (m := m) L tech.good n -
        successProb (X := Y) (m := m) L tech.good n|)) :
    Breaks tech.D (iidSamplesEnsemble X m) (iidSamplesEnsemble Y m) := by
  -- The induced distinguisher is in `tech.D` by boundedness.
  have hmem : learnerDistinguisher (L := L) (good := tech.good) ∈ tech.D :=
    tech.bounded L hL
  refine ⟨learnerDistinguisher (L := L) (good := tech.good), hmem, ?_⟩
  -- Rewrite advantage as the absolute success-gap.
  have hEq :
      advantageEnsemble (learnerDistinguisher (L := L) (good := tech.good))
          (iidSamplesEnsemble X m) (iidSamplesEnsemble Y m) =
        fun n =>
          |successProb (X := X) (m := m) L tech.good n -
            successProb (X := Y) (m := m) L tech.good n| := by
    funext n
    simpa using
      (LearningGame.advantage_learnerDistinguisher_eq (X := X) (Y := Y) (m := m) (L := L)
        (good := tech.good) n)
  simpa [hEq] using hGap

/--
Magnification template: if "breaking indistinguishability for `tech.D`" implies some consequence,
then the existence of a learner in `tech` with non-negligible success-gap implies that consequence.
-/
theorem magnify
    (tech : LearningTechnique (Example := Example) (Hyp := Hyp) (m := m))
    (X Y : Ensemble Example)
    {Consequence : Prop}
    (hConseq :
      Breaks tech.D (iidSamplesEnsemble X m) (iidSamplesEnsemble Y m) →
        Consequence) :
    (∃ L ∈ tech.learners, ¬Negligible (fun n =>
      |successProb (X := X) (m := m) L tech.good n -
        successProb (X := Y) (m := m) L tech.good n|)) →
      Consequence := by
  rintro ⟨L, hL, hGap⟩
  exact hConseq (breaks_of_nonNegligible_successGap (tech := tech) (X := X) (Y := Y) hL hGap)

/-! ## Contrastive Learning Application -/

namespace ContrastiveLearning

variable {X : ℕ → Type u} [∀ n, MeasurableSpace (X n)]

abbrev PairExample : ℕ → Type u :=
  fun n => X n × X n

noncomputable instance : ∀ n, MeasurableSpace (PairExample (X := X) n) :=
  fun _ => inferInstance

/-! ### Product-of-marginals negative distribution -/

noncomputable def marginalLeft (J : Ensemble (PairExample (X := X))) : Ensemble X :=
  fun n => ProbabilityMeasure.map (J n) (measurable_fst.aemeasurable)

noncomputable def marginalRight (J : Ensemble (PairExample (X := X))) : Ensemble X :=
  fun n => ProbabilityMeasure.map (J n) (measurable_snd.aemeasurable)

/--
The standard "negative pairs" distribution obtained by independently sampling from the two marginals
of `J`. This models the common "shuffle negatives" construction in contrastive learning.
-/
noncomputable def productOfMarginals (J : Ensemble (PairExample (X := X))) :
    Ensemble (PairExample (X := X)) :=
  fun n => ProbabilityMeasure.prod (marginalLeft (X := X) J n) (marginalRight (X := X) J n)

/-! ### Barrier and magnification -/

variable {Hyp : ℕ → Type v} {m : ℕ → ℕ}

abbrev Technique :=
  LearningTechnique (Example := PairExample (X := X)) (Hyp := Hyp) (m := m)

/--
**Contrastive magnification (break form)**: if a learner in `tech` has a non-negligible success-gap
between positives `J` and negatives `productOfMarginals J`, then `tech.D` breaks indistinguishability
of the corresponding i.i.d. sample ensembles.
-/
theorem breaks_productOfMarginals_of_successGap
    (tech : Technique (X := X) (Hyp := Hyp) (m := m))
    (J : Ensemble (PairExample (X := X)))
    {L : Learner (PairExample (X := X)) Hyp m} (hL : L ∈ tech.learners)
    (hGap : ¬Negligible (fun n =>
      |successProb (X := J) (m := m) L tech.good n -
        successProb (X := productOfMarginals (X := X) J) (m := m) L tech.good n|)) :
    Breaks (Example := PairExample (X := X)) (m := m) tech.D
      (iidSamplesEnsemble J m)
      (iidSamplesEnsemble (productOfMarginals (X := X) J) m) := by
  simpa using
    (breaks_of_nonNegligible_successGap (tech := tech)
      (X := J) (Y := productOfMarginals (X := X) J) (L := L) hL hGap)

/--
**Contrastive barrier (negligible gap)**: if positives and negatives are indistinguishable for `tech.D`,
then every learner in `tech` has only a negligible success-gap.
-/
theorem barrier_productOfMarginals
    (tech : Technique (X := X) (Hyp := Hyp) (m := m))
    (J : Ensemble (PairExample (X := X)))
    (hInd : Indistinguishable tech.D (iidSamplesEnsemble J m)
      (iidSamplesEnsemble (productOfMarginals (X := X) J) m)) :
    ∀ L ∈ tech.learners,
      Negligible (fun n =>
        |successProb (X := J) (m := m) L tech.good n -
          successProb (X := productOfMarginals (X := X) J) (m := m) L tech.good n|) := by
  simpa using
    (learning_barrier (tech := tech)
      (X := J) (Y := productOfMarginals (X := X) J) hInd)

end ContrastiveLearning

end LearningBarrier

end Pseudorandomness
