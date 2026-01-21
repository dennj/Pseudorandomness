import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
  Cryptographic Foundations for Pseudorandomness
  ==============================================

  This file consolidates the foundational components for cryptographic pseudorandomness:

  1. **CryptoMeasure**: Measure-theoretic primitives for computational pseudorandomness
     - Ensembles (families of probability measures)
     - Distinguishers and acceptance probability
     - Negligible functions and computational indistinguishability
     - I.i.d. sampling

  2. **LearningGame**: Learning as distinguishing (sample-based reductions)
     - Learners and success predicates
     - Reduction from learning to distinguishing

  3. **CLWE**: Continuous LWE as an ensemble
     - Abstract CLWE sample distributions
     - Real and random ensembles

  4. **CLWEGame**: CLWE sample games
     - Connection between indistinguishability and learning hardness
-/

namespace Pseudorandomness

open Filter

/-! ============================================================================
    Part 1: CryptoMeasure - Computational Pseudorandomness Layer
    ============================================================================ -/

namespace CryptoMeasure

open MeasureTheory

/-! ## Ensembles and distinguishers -/

abbrev Ensemble (α : ℕ → Type*) [∀ n, MeasurableSpace (α n)] : Type _ :=
  ∀ n : ℕ, MeasureTheory.ProbabilityMeasure (α n)

abbrev Distinguisher (α : ℕ → Type*) : Type _ :=
  ∀ n : ℕ, α n → Bool

/-! ## Acceptance probability and advantage -/

noncomputable section

variable {α : Type*} [MeasurableSpace α]

def acceptENNReal (d : α → Bool) (μ : ProbabilityMeasure α) : ENNReal :=
  (μ : Measure α) (d ⁻¹' {true})

theorem acceptENNReal_le_one (d : α → Bool) (μ : ProbabilityMeasure α) : acceptENNReal d μ ≤ 1 := by
  classical
  have h : (μ : Measure α) (d ⁻¹' {true}) ≤ (μ : Measure α) Set.univ := by
    exact measure_mono (by intro x _hx; trivial)
  simpa [acceptENNReal] using (h.trans_eq (by simp))

def acceptProb (d : α → Bool) (μ : ProbabilityMeasure α) : ℝ :=
  ENNReal.toReal (acceptENNReal d μ)

theorem acceptProb_nonneg (d : α → Bool) (μ : ProbabilityMeasure α) : 0 ≤ acceptProb d μ := by
  simp [acceptProb, acceptENNReal]

theorem acceptProb_le_one (d : α → Bool) (μ : ProbabilityMeasure α) : acceptProb d μ ≤ 1 := by
  have hle : acceptENNReal d μ ≤ 1 := acceptENNReal_le_one (d := d) (μ := μ)
  have hto : ENNReal.toReal (acceptENNReal d μ) ≤ ENNReal.toReal (1 : ENNReal) :=
    ENNReal.toReal_mono (by simp) hle
  simpa [acceptProb] using hto

def advantage (d : α → Bool) (μ ν : ProbabilityMeasure α) : ℝ :=
  |acceptProb d μ - acceptProb d ν|

theorem advantage_nonneg (d : α → Bool) (μ ν : ProbabilityMeasure α) : 0 ≤ advantage d μ ν := by
  simp [advantage]

theorem advantage_symm (d : α → Bool) (μ ν : ProbabilityMeasure α) :
    advantage d μ ν = advantage d ν μ := by
  simp [advantage, abs_sub_comm]

theorem advantage_triangle (d : α → Bool) (μ ν ρ : ProbabilityMeasure α) :
    advantage d μ ρ ≤ advantage d μ ν + advantage d ν ρ := by
  simpa [advantage] using abs_sub_le (acceptProb d μ) (acceptProb d ν) (acceptProb d ρ)

/-! ## Negligible functions and computational indistinguishability -/

def Negligible (f : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, Tendsto (fun n => |f n| * ((n + 1 : ℕ) : ℝ) ^ k) atTop (nhds 0)

theorem negligible_zero : Negligible (fun _n => (0 : ℝ)) := by
  intro k
  simp

theorem Negligible.add {f g : ℕ → ℝ} (hf : Negligible f) (hg : Negligible g) :
    Negligible (fun n => f n + g n) := by
  intro k
  have hsum :
      Tendsto (fun n => |f n| * ((n + 1 : ℕ) : ℝ) ^ k + |g n| * ((n + 1 : ℕ) : ℝ) ^ k) atTop
        (nhds 0) := by
    simpa using (hf k).add (hg k)
  have hnonneg : ∀ n, 0 ≤ |f n + g n| * ((n + 1 : ℕ) : ℝ) ^ k := by
    intro n
    have : 0 ≤ ((n + 1 : ℕ) : ℝ) ^ k := by positivity
    exact mul_nonneg (abs_nonneg _) this
  have hle : ∀ n,
      |f n + g n| * ((n + 1 : ℕ) : ℝ) ^ k ≤
        |f n| * ((n + 1 : ℕ) : ℝ) ^ k + |g n| * ((n + 1 : ℕ) : ℝ) ^ k := by
    intro n
    have hP : 0 ≤ ((n + 1 : ℕ) : ℝ) ^ k := by positivity
    have habs : |f n + g n| ≤ |f n| + |g n| := abs_add_le _ _
    calc
      |f n + g n| * ((n + 1 : ℕ) : ℝ) ^ k
          ≤ (|f n| + |g n|) * ((n + 1 : ℕ) : ℝ) ^ k := by
              exact mul_le_mul_of_nonneg_right habs hP
      _ = |f n| * ((n + 1 : ℕ) : ℝ) ^ k + |g n| * ((n + 1 : ℕ) : ℝ) ^ k := by
            simp [add_mul]
  exact squeeze_zero (fun n => hnonneg n) (fun n => hle n) hsum

theorem Negligible.of_eventually_abs_le {f g : ℕ → ℝ} (hg : Negligible g)
    (h : ∀ᶠ n in atTop, |f n| ≤ |g n|) : Negligible f := by
  intro k
  have hnonneg : ∀ n, 0 ≤ |f n| * ((n + 1 : ℕ) : ℝ) ^ k := by
    intro n
    have : 0 ≤ ((n + 1 : ℕ) : ℝ) ^ k := by positivity
    exact mul_nonneg (abs_nonneg _) this
  have hle : ∀ᶠ n in atTop,
      |f n| * ((n + 1 : ℕ) : ℝ) ^ k ≤ |g n| * ((n + 1 : ℕ) : ℝ) ^ k := by
    filter_upwards [h] with n hn
    have hP : 0 ≤ ((n + 1 : ℕ) : ℝ) ^ k := by positivity
    exact mul_le_mul_of_nonneg_right hn hP
  exact squeeze_zero' (hf := (Eventually.of_forall hnonneg)) (hft := hle) (hg k)

def advantageEnsemble {α : ℕ → Type*} [∀ n, MeasurableSpace (α n)]
    (d : Distinguisher α) (X Y : Ensemble α) : ℕ → ℝ :=
  fun n => advantage (d n) (X n) (Y n)

def Indistinguishable {α : ℕ → Type*} [∀ n, MeasurableSpace (α n)]
    (D : Set (Distinguisher α)) (X Y : Ensemble α) : Prop :=
  ∀ d ∈ D, Negligible (advantageEnsemble d X Y)

theorem Indistinguishable.refl {α : ℕ → Type*} [∀ n, MeasurableSpace (α n)]
    (D : Set (Distinguisher α)) (X : Ensemble α) :
    Indistinguishable D X X := by
  intro d hd
  have : advantageEnsemble d X X = fun _n => (0 : ℝ) := by
    funext n
    simp [advantageEnsemble, advantage]
  simpa [this] using negligible_zero

theorem Indistinguishable.symm {α : ℕ → Type*} [∀ n, MeasurableSpace (α n)]
    {D : Set (Distinguisher α)} {X Y : Ensemble α}
    (h : Indistinguishable D X Y) : Indistinguishable D Y X := by
  intro d hd
  have hneg := h d hd
  have hEq : advantageEnsemble d Y X = advantageEnsemble d X Y := by
    funext n
    simpa [advantageEnsemble] using (advantage_symm (d := d n) (μ := X n) (ν := Y n)).symm
  simpa [hEq] using hneg

theorem Indistinguishable.trans {α : ℕ → Type*} [∀ n, MeasurableSpace (α n)]
    {D : Set (Distinguisher α)} {X Y Z : Ensemble α}
    (hXY : Indistinguishable D X Y) (hYZ : Indistinguishable D Y Z) :
    Indistinguishable D X Z := by
  intro d hd
  have hsum : Negligible (fun n => advantage (d n) (X n) (Y n) + advantage (d n) (Y n) (Z n)) := by
    simpa [advantageEnsemble] using Negligible.add (hXY d hd) (hYZ d hd)
  refine Negligible.of_eventually_abs_le hsum ?_
  refine Eventually.of_forall ?_
  intro n
  have htri :
      advantage (d n) (X n) (Z n) ≤ advantage (d n) (X n) (Y n) + advantage (d n) (Y n) (Z n) :=
    advantage_triangle (d := d n) (μ := X n) (ν := Y n) (ρ := Z n)
  have hnonnegL : 0 ≤ advantage (d n) (X n) (Z n) := advantage_nonneg (d := d n) (μ := X n) (ν := Z n)
  have hnonnegR : 0 ≤ advantage (d n) (X n) (Y n) + advantage (d n) (Y n) (Z n) := by
    have h1 : 0 ≤ advantage (d n) (X n) (Y n) := advantage_nonneg (d := d n) (μ := X n) (ν := Y n)
    have h2 : 0 ≤ advantage (d n) (Y n) (Z n) := advantage_nonneg (d := d n) (μ := Y n) (ν := Z n)
    linarith
  have hle :
      advantageEnsemble d X Z n ≤ advantage (d n) (X n) (Y n) + advantage (d n) (Y n) (Z n) := by
    simpa [advantageEnsemble] using htri
  have hnonnegEnsemble : 0 ≤ advantageEnsemble d X Z n := by
    simpa [advantageEnsemble] using advantage_nonneg (d := d n) (μ := X n) (ν := Z n)
  have hleAbs :
      |advantageEnsemble d X Z n| ≤
        |advantage (d n) (X n) (Y n) + advantage (d n) (Y n) (Z n)| := by
    simpa [abs_of_nonneg hnonnegEnsemble, abs_of_nonneg hnonnegR] using hle
  simpa using hleAbs

/-! ## I.i.d. sampling (finite products) -/

noncomputable def iidSamples {α : Type*} [MeasurableSpace α] (μ : ProbabilityMeasure α) (m : ℕ) :
    ProbabilityMeasure (Fin m → α) :=
  ProbabilityMeasure.pi (fun _ : Fin m => μ)

noncomputable def iidSamplesEnsemble {α : ℕ → Type*} [∀ n, MeasurableSpace (α n)]
    (X : Ensemble α) (m : ℕ → ℕ) : Ensemble (fun n => Fin (m n) → α n) :=
  fun n => iidSamples (μ := X n) (m := m n)

end

end CryptoMeasure

/-! ============================================================================
    Part 2: LearningGame - Learning as Distinguishing
    ============================================================================ -/

namespace LearningGame

open Filter
open CryptoMeasure

universe u v

abbrev Samples (Example : ℕ → Type u) (m : ℕ → ℕ) : ℕ → Type u :=
  fun n => Fin (m n) → Example n

abbrev Learner (Example : ℕ → Type u) (Hyp : ℕ → Type v) (m : ℕ → ℕ) : Type _ :=
  ∀ n : ℕ, Samples Example m n → Hyp n

abbrev SuccessPred (Hyp : ℕ → Type v) : Type _ :=
  ∀ n : ℕ, Hyp n → Bool

def learnerDistinguisher {Example : ℕ → Type u} {Hyp : ℕ → Type v} {m : ℕ → ℕ}
    (L : Learner Example Hyp m) (good : SuccessPred Hyp) :
    Distinguisher (Samples Example m) :=
  fun n s => good n (L n s)

noncomputable def successProb {Example : ℕ → Type u} {Hyp : ℕ → Type v} [∀ n, MeasurableSpace (Example n)]
    {m : ℕ → ℕ} (X : Ensemble Example) (L : Learner Example Hyp m) (good : SuccessPred Hyp) : ℕ → ℝ :=
  fun n =>
    letI : MeasurableSpace (Samples Example m n) := inferInstance
    acceptProb (learnerDistinguisher (L := L) (good := good) n) (iidSamples (μ := X n) (m := m n))

theorem advantage_learnerDistinguisher_eq {Example : ℕ → Type u} {Hyp : ℕ → Type v}
    [∀ n, MeasurableSpace (Example n)]
    {m : ℕ → ℕ} (X Y : Ensemble Example) (L : Learner Example Hyp m) (good : SuccessPred Hyp) (n : ℕ) :
    advantageEnsemble (learnerDistinguisher (L := L) (good := good)) (iidSamplesEnsemble X m)
        (iidSamplesEnsemble Y m) n =
      |successProb (X := X) (m := m) L good n - successProb (X := Y) (m := m) L good n| := by
  letI : MeasurableSpace (Samples Example m n) := inferInstance
  simp [advantageEnsemble, advantage, successProb, iidSamplesEnsemble, iidSamples]

theorem advantage_ge_of_successProb_bounds {Example : ℕ → Type u} {Hyp : ℕ → Type v}
    [∀ n, MeasurableSpace (Example n)]
    {m : ℕ → ℕ} (X Y : Ensemble Example) (L : Learner Example Hyp m) (good : SuccessPred Hyp)
    {n : ℕ} {p q : ℝ}
    (hp : p ≤ successProb (X := X) (m := m) L good n)
    (hq : successProb (X := Y) (m := m) L good n ≤ q) :
    p - q ≤ advantageEnsemble (learnerDistinguisher (L := L) (good := good)) (iidSamplesEnsemble X m)
      (iidSamplesEnsemble Y m) n := by
  letI : MeasurableSpace (Samples Example m n) := inferInstance
  have hlin : p - q ≤ successProb (X := X) (m := m) L good n - successProb (X := Y) (m := m) L good n := by
    linarith
  -- Drop into the definition of advantage.
  have habs : successProb (X := X) (m := m) L good n - successProb (X := Y) (m := m) L good n ≤
      |successProb (X := X) (m := m) L good n - successProb (X := Y) (m := m) L good n| :=
    le_abs_self _
  have :
      p - q ≤ |successProb (X := X) (m := m) L good n - successProb (X := Y) (m := m) L good n| :=
    le_trans hlin habs
  simpa [advantageEnsemble, advantage, successProb, iidSamplesEnsemble, iidSamples, learnerDistinguisher] using this

theorem negligible_abs_successProb_sub_of_indistinguishable {Example : ℕ → Type u} {Hyp : ℕ → Type v}
    [∀ n, MeasurableSpace (Example n)]
    {m : ℕ → ℕ} {D : Set (Distinguisher (Samples Example m))} (X Y : Ensemble Example)
    (L : Learner Example Hyp m) (good : SuccessPred Hyp)
    (hInd :
      Indistinguishable D (iidSamplesEnsemble X m) (iidSamplesEnsemble Y m))
    (hmem : learnerDistinguisher (L := L) (good := good) ∈ D) :
    Negligible
      (fun n =>
        |successProb (X := X) (m := m) L good n - successProb (X := Y) (m := m) L good n|) := by
  have hNeg :=
    hInd (learnerDistinguisher (L := L) (good := good)) hmem
  have hEq :
      advantageEnsemble (learnerDistinguisher (L := L) (good := good))
          (iidSamplesEnsemble X m) (iidSamplesEnsemble Y m) =
        fun n =>
          |successProb (X := X) (m := m) L good n - successProb (X := Y) (m := m) L good n| := by
    funext n
    simpa using
      (advantage_learnerDistinguisher_eq (X := X) (Y := Y) (m := m) (L := L) (good := good) n)
  simpa [hEq] using hNeg

end LearningGame

/-! ============================================================================
    Part 3: CLWE - Continuous LWE as an Ensemble
    ============================================================================ -/

namespace CLWE

open MeasureTheory
open CryptoMeasure

universe u v w

variable {A : ℕ → Type u} {S : ℕ → Type v} {T : ℕ → Type w}
variable [∀ n, MeasurableSpace (A n)] [∀ n, MeasurableSpace (T n)]
variable [∀ n, Add (T n)]

/-- A single CLWE sample is a pair `(a, b)` with `a : A n` and `b : T n`. -/
abbrev Sample (n : ℕ) : Type _ :=
  A n × T n

/--
Given a secret `s : S n`, the CLWE sample map takes `(a, e)` to `(a, φ a s + e)`.

We keep `φ` abstract; concrete instances will use an inner product followed by a quotient/map.
-/
def sampleMap (φ : ∀ n, A n → S n → T n) (s : ∀ n, S n) (n : ℕ) :
    (A n × T n) → (Sample (A := A) (T := T) n) :=
  fun ae => (ae.1, φ n ae.1 (s n) + ae.2)

/--
The "real" CLWE ensemble generated from:

- `aDist`: distribution of `a`
- `noise`: distribution of noise `e`
- `φ`: the structured label map
- `s`: the secret

The only nontrivial requirement is that the sampling map is `AEMeasurable` with respect to the
product distribution on `(a, e)`.
-/
noncomputable def realEnsemble
    (aDist : ∀ n, ProbabilityMeasure (A n))
    (noise : ∀ n, ProbabilityMeasure (T n))
    (φ : ∀ n, A n → S n → T n)
    (s : ∀ n, S n)
    (hMap : ∀ n,
      AEMeasurable (sampleMap (A := A) (S := S) (T := T) φ s n)
        (ProbabilityMeasure.prod (aDist n) (noise n))) :
    Ensemble (fun n => Sample (A := A) (T := T) n) :=
  fun n =>
    ProbabilityMeasure.map (ProbabilityMeasure.prod (aDist n) (noise n)) (hMap n)

/--
The "random" CLWE ensemble: `a` from `aDist` and `b` from an (intended) uniform distribution
on the label space `T n`, independently.
-/
noncomputable def randomEnsemble
    (aDist : ∀ n, ProbabilityMeasure (A n))
    (uniform : ∀ n, ProbabilityMeasure (T n)) :
    Ensemble (fun n => Sample (A := A) (T := T) n) :=
  fun n => ProbabilityMeasure.prod (aDist n) (uniform n)

end CLWE

/-! ============================================================================
    Part 4: CLWEGame - CLWE Sample Games
    ============================================================================ -/

namespace CLWEGame

open CryptoMeasure LearningGame CLWE
open MeasureTheory

universe u v w

variable {A : ℕ → Type u} {S : ℕ → Type v} {T : ℕ → Type w}
variable [∀ n, MeasurableSpace (A n)] [∀ n, MeasurableSpace (T n)]
variable [∀ n, Add (T n)]

variable (aDist : ∀ n, ProbabilityMeasure (A n))
variable (noise uniform : ∀ n, ProbabilityMeasure (T n))
variable (φ : ∀ n, A n → S n → T n) (s : ∀ n, S n)
variable (hMap : ∀ n,
  AEMeasurable (CLWE.sampleMap (A := A) (S := S) (T := T) φ s n)
    (ProbabilityMeasure.prod (aDist n) (noise n)))

variable {m : ℕ → ℕ}
variable {Hyp : ℕ → Type*}
variable {D : Set (Distinguisher (Samples (fun n => CLWE.Sample (A := A) (T := T) n) m))}

/--
If the `m(n)`-sample CLWE-real ensemble is indistinguishable from the random ensemble for a class
of distinguishers `D`, then any learner whose induced distinguisher is in `D` has only negligible
gap in success probability between the two worlds.
-/
theorem negligible_success_gap_of_clwe_indistinguishable
    (hInd :
      Indistinguishable D
        (iidSamplesEnsemble (CLWE.realEnsemble (A := A) (S := S) (T := T) aDist noise φ s hMap) m)
        (iidSamplesEnsemble (CLWE.randomEnsemble (A := A) (T := T) aDist uniform) m))
    (L : Learner (fun n => CLWE.Sample (A := A) (T := T) n) Hyp m)
    (good : SuccessPred Hyp)
    (hmem : learnerDistinguisher (L := L) (good := good) ∈ D) :
    Negligible (fun n =>
      |successProb
          (X := CLWE.realEnsemble (A := A) (S := S) (T := T) aDist noise φ s hMap)
          (m := m) L good n -
        successProb
          (X := CLWE.randomEnsemble (A := A) (T := T) aDist uniform)
          (m := m) L good n|) := by
  simpa using
    (LearningGame.negligible_abs_successProb_sub_of_indistinguishable
      (X := CLWE.realEnsemble (A := A) (S := S) (T := T) aDist noise φ s hMap)
      (Y := CLWE.randomEnsemble (A := A) (T := T) aDist uniform)
      (m := m) (D := D) (L := L) (good := good) hInd hmem)

end CLWEGame

end Pseudorandomness
