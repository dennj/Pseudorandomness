import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
  Computational Pseudorandomness Layer (Distributions / Ensembles)
  ===============================================================

  This file adds a lightweight, mathlib-friendly layer for “real” cryptographic
  pseudorandomness:

  - discrete distributions via `PMF`;
  - distribution ensembles indexed by a security parameter `n : ℕ`;
  - (oracle) distinguishers and their distinguishing advantage;
  - a `Negligible` predicate and computational indistinguishability;
  - packaged notions of PRG and PRF as indistinguishability statements;
  - a basic “hybrid argument” inequality.

  This layer is intentionally abstract: “resource-bounded” means “belongs to a set `D`”
  (matching the project’s observer-class pattern), leaving complexity bounds to be
  instantiated elsewhere.
-/

namespace Pseudorandomness

open scoped BigOperators
open Filter

namespace Crypto

/-! ## Ensembles and distinguishers -/

/-- A distribution ensemble indexed by the security parameter `n`. -/
abbrev Ensemble (α : ℕ → Type*) : Type _ :=
  ∀ n : ℕ, PMF (α n)

/-- A (non-uniform) distinguisher for an ensemble. -/
abbrev Distinguisher (α : ℕ → Type*) : Type _ :=
  ∀ n : ℕ, α n → Bool

/--
An oracle distinguisher: the “sample” to be distinguished is itself an oracle/function.

This models oracle access extensionally (as a parameter of type `dom n → cod n`).
More refined interactive models can be layered on later.
-/
abbrev OracleDistinguisher (dom cod : ℕ → Type*) : Type _ :=
  Distinguisher (fun n => dom n → cod n)

/-! ## Query-bounded oracle access (interactive, deterministic) -/

/--
A deterministic oracle strategy making exactly `q` (adaptive) queries.

This is a simple decision-tree model:
- at depth `0`, output a `Bool`;
- at depth `q+1`, pick a query `x : Dom`, receive an answer `y : Cod`,
  and continue with a `q`-query strategy depending on `y`.
-/
inductive OracleStrategy (Dom Cod : Type*) : ℕ → Type _
  | done : Bool → OracleStrategy Dom Cod 0
  | query {q : ℕ} : Dom → (Cod → OracleStrategy Dom Cod q) → OracleStrategy Dom Cod (q + 1)

/-- Run a query strategy against a concrete oracle `Dom → Cod`. -/
def OracleStrategy.run {Dom Cod : Type*} : ∀ {q : ℕ}, OracleStrategy Dom Cod q → (Dom → Cod) → Bool
  | 0, OracleStrategy.done b, _oracle => b
  | q + 1, OracleStrategy.query x k, oracle => OracleStrategy.run (q := q) (k (oracle x)) oracle

/--
An `n`-indexed family of query-bounded oracle strategies.

The query bound itself can depend on `n` (e.g. polynomially).
-/
abbrev QueryBoundedOracleDistinguisher (dom cod : ℕ → Type*) (q : ℕ → ℕ) : Type _ :=
  ∀ n : ℕ, OracleStrategy (dom n) (cod n) (q n)

/-- Interpret a query-bounded strategy as an extensional oracle distinguisher. -/
def QueryBoundedOracleDistinguisher.toOracleDistinguisher {dom cod : ℕ → Type*} {q : ℕ → ℕ} :
    QueryBoundedOracleDistinguisher dom cod q → OracleDistinguisher dom cod :=
  fun d n oracle => OracleStrategy.run (d n) oracle

/-! ## Acceptance probability and advantage -/

noncomputable section

variable {α : Type*}

/-- Acceptance probability (as `ENNReal`) of `d` on input distributed as `p`. -/
def acceptENNReal (d : α → Bool) (p : PMF α) : ENNReal :=
  ∑' x, if d x then p x else 0

theorem acceptENNReal_le_one (d : α → Bool) (p : PMF α) : acceptENNReal d p ≤ 1 := by
  classical
  -- Pointwise bound by `p`, then sum.
  have hle : (fun x => (if d x then p x else 0)) ≤ p := by
    intro x
    by_cases hx : d x
    · simp [hx]
    · simp [hx]
  have : (∑' x, if d x then p x else 0) ≤ ∑' x, p x := by
    exact ENNReal.tsum_le_tsum hle
  simpa [acceptENNReal, p.tsum_coe] using this

/-- Acceptance probability (as a real number in `[0,1]`). -/
def acceptProb (d : α → Bool) (p : PMF α) : ℝ :=
  ENNReal.toReal (acceptENNReal d p)

theorem acceptProb_nonneg (d : α → Bool) (p : PMF α) : 0 ≤ acceptProb d p := by
  simp [acceptProb, acceptENNReal]

theorem acceptProb_le_one (d : α → Bool) (p : PMF α) : acceptProb d p ≤ 1 := by
  have hle : acceptENNReal d p ≤ 1 := acceptENNReal_le_one d p
  -- `toReal` is monotone on finite values; here everything is ≤ 1 = `ENNReal.ofReal 1`.
  have hle' : acceptENNReal d p ≤ ENNReal.ofReal (1 : ℝ) := by
    simpa using hle
  simpa [acceptProb] using ENNReal.toReal_le_of_le_ofReal (show (0 : ℝ) ≤ 1 by linarith) hle'

/-- Distinguishing advantage of `d` between `p` and `q`. -/
def advantage (d : α → Bool) (p q : PMF α) : ℝ :=
  |acceptProb d p - acceptProb d q|

theorem advantage_nonneg (d : α → Bool) (p q : PMF α) : 0 ≤ advantage d p q := by
  simp [advantage]

theorem advantage_symm (d : α → Bool) (p q : PMF α) : advantage d p q = advantage d q p := by
  simp [advantage, abs_sub_comm]

theorem advantage_triangle (d : α → Bool) (p q r : PMF α) :
    advantage d p r ≤ advantage d p q + advantage d q r := by
  -- `|a - c| ≤ |a - b| + |b - c|`
  simpa [advantage] using abs_sub_le (acceptProb d p) (acceptProb d q) (acceptProb d r)

/-! ## Negligible functions and computational indistinguishability -/

/--
`Negligible f` means `f` vanishes faster than any polynomial:
for each `k`, `|f n| * (n+1)^k → 0`.
-/
def Negligible (f : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, Tendsto (fun n => |f n| * ((n + 1 : ℕ) : ℝ) ^ k) atTop (nhds 0)

theorem negligible_zero : Negligible (fun _n => (0 : ℝ)) := by
  intro k
  simp

theorem Negligible.add {f g : ℕ → ℝ} (hf : Negligible f) (hg : Negligible g) :
    Negligible (fun n => f n + g n) := by
  intro k
  -- Squeeze `|f+g| * P` by `(|f|*P + |g|*P)` and use `tendsto_add`.
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
  have hgk := hg k
  have hnonneg : ∀ n, 0 ≤ |f n| * ((n + 1 : ℕ) : ℝ) ^ k := by
    intro n
    have : 0 ≤ ((n + 1 : ℕ) : ℝ) ^ k := by positivity
    exact mul_nonneg (abs_nonneg _) this
  have hle : ∀ᶠ n in atTop,
      |f n| * ((n + 1 : ℕ) : ℝ) ^ k ≤ |g n| * ((n + 1 : ℕ) : ℝ) ^ k := by
    filter_upwards [h] with n hn
    have hP : 0 ≤ ((n + 1 : ℕ) : ℝ) ^ k := by positivity
    exact mul_le_mul_of_nonneg_right hn hP
  exact squeeze_zero' (hf := (Eventually.of_forall hnonneg)) (hft := hle) hgk

/-- Advantage of a distinguisher between two ensembles, as a function of `n`. -/
def advantageEnsemble {α : ℕ → Type*} (d : Distinguisher α) (X Y : Ensemble α) : ℕ → ℝ :=
  fun n => advantage (d n) (X n) (Y n)

/--
Computational indistinguishability of ensembles relative to a class of distinguishers `D`.
-/
def Indistinguishable {α : ℕ → Type*} (D : Set (Distinguisher α)) (X Y : Ensemble α) : Prop :=
  ∀ d ∈ D, Negligible (advantageEnsemble d X Y)

theorem Negligible.sum_range {f : ℕ → ℕ → ℝ} : ∀ m : ℕ,
    (∀ i < m, Negligible (f i)) → Negligible (fun n => Finset.sum (Finset.range m) (fun i => f i n))
  | 0, _hf => by
      simpa using negligible_zero
  | Nat.succ m, hf => by
      have hinit : ∀ i < m, Negligible (f i) := by
        intro i hi
        exact hf i (Nat.lt_trans hi (Nat.lt_succ_self m))
      have hlast : Negligible (f m) :=
        hf m (Nat.lt_succ_self m)
      have hsum : Negligible (fun n => Finset.sum (Finset.range m) (fun i => f i n)) :=
        Negligible.sum_range (f := f) m hinit
      have hadd :
          Negligible
            (fun n =>
              Finset.sum (Finset.range m) (fun i => f i n) + f m n) :=
        Negligible.add hsum hlast
      simpa [Finset.sum_range_succ, add_comm, add_left_comm, add_assoc] using hadd

theorem Indistinguishable.refl {α : ℕ → Type*} (D : Set (Distinguisher α)) (X : Ensemble α) :
    Indistinguishable D X X := by
  intro d hd
  -- `advantage` is `|a-a|`.
  have : advantageEnsemble d X X = fun _n => (0 : ℝ) := by
    funext n
    simp [advantageEnsemble, advantage]
  simpa [this] using negligible_zero

theorem Indistinguishable.symm {α : ℕ → Type*} {D : Set (Distinguisher α)} {X Y : Ensemble α}
    (h : Indistinguishable D X Y) : Indistinguishable D Y X := by
  intro d hd
  have hneg := h d hd
  have hEq : advantageEnsemble d Y X = advantageEnsemble d X Y := by
    funext n
    simpa [advantageEnsemble] using
      (advantage_symm (d := d n) (p := Y n) (q := X n))
  simpa [hEq] using hneg

theorem Indistinguishable.trans {α : ℕ → Type*} {D : Set (Distinguisher α)} {X Y Z : Ensemble α}
    (hXY : Indistinguishable D X Y) (hYZ : Indistinguishable D Y Z) :
    Indistinguishable D X Z := by
  intro d hd
  have hsum : Negligible (fun n => advantage (d n) (X n) (Y n) + advantage (d n) (Y n) (Z n)) := by
    simpa [advantageEnsemble] using (Negligible.add (hXY d hd) (hYZ d hd))
  refine Negligible.of_eventually_abs_le hsum ?_
  refine Eventually.of_forall ?_
  intro n
  have htri :
      advantage (d n) (X n) (Z n) ≤ advantage (d n) (X n) (Y n) + advantage (d n) (Y n) (Z n) :=
    advantage_triangle (d := d n) (p := X n) (q := Y n) (r := Z n)
  have hnonnegL : 0 ≤ advantageEnsemble d X Z n := by
    simpa [advantageEnsemble] using
      advantage_nonneg (d := d n) (p := X n) (q := Z n)
  have hnonnegR : 0 ≤ advantage (d n) (X n) (Y n) + advantage (d n) (Y n) (Z n) := by
    have h1 : 0 ≤ advantage (d n) (X n) (Y n) := advantage_nonneg (d := d n) (p := X n) (q := Y n)
    have h2 : 0 ≤ advantage (d n) (Y n) (Z n) := advantage_nonneg (d := d n) (p := Y n) (q := Z n)
    linarith
  -- Both sides are nonnegative, so we can drop `abs`.
  have : advantageEnsemble d X Z n ≤ advantage (d n) (X n) (Y n) + advantage (d n) (Y n) (Z n) := by
    simpa [advantageEnsemble] using htri
  simpa [abs_of_nonneg hnonnegL, abs_of_nonneg hnonnegR] using this

theorem Indistinguishable.of_hybrids {α : ℕ → Type*} (D : Set (Distinguisher α))
    (X : ℕ → Ensemble α) (m : ℕ)
    (h : ∀ i < m, Indistinguishable D (X i) (X (i + 1))) :
    Indistinguishable D (X 0) (X m) := by
  induction m with
  | zero =>
      simpa using (Indistinguishable.refl (D := D) (X := X 0))
  | succ m ih =>
      have hinit : ∀ i < m, Indistinguishable D (X i) (X (i + 1)) := by
        intro i hi
        exact h i (Nat.lt_trans hi (Nat.lt_succ_self m))
      have hprev : Indistinguishable D (X 0) (X m) := ih hinit
      have hlast : Indistinguishable D (X m) (X (m + 1)) :=
        h m (Nat.lt_succ_self m)
      simpa using Indistinguishable.trans hprev hlast

/-! ## PRG and PRF as indistinguishability statements -/

section PRG

variable {Seed Out : ℕ → Type*}
variable [∀ n, Fintype (Seed n)] [∀ n, Nonempty (Seed n)]
variable [∀ n, Fintype (Out n)] [∀ n, Nonempty (Out n)]

/-- The output distribution of a (non-uniform) PRG `G` on uniform seeds. -/
noncomputable def prgOutput (G : ∀ n, Seed n → Out n) : Ensemble Out :=
  fun n => (PMF.uniformOfFintype (Seed n)).map (G n)

/-- The uniform output ensemble on `Out n`. -/
noncomputable def uniformEnsemble (Out : ℕ → Type*) [∀ n, Fintype (Out n)] [∀ n, Nonempty (Out n)] :
    Ensemble Out :=
  fun n => PMF.uniformOfFintype (Out n)

/-- `G` is a PRG against distinguishers in `D` if its output is indistinguishable from uniform. -/
def IsPRG (D : Set (Distinguisher Out)) (G : ∀ n, Seed n → Out n) : Prop :=
  Indistinguishable D (prgOutput (Seed := Seed) (Out := Out) G) (uniformEnsemble Out)

end PRG

section PRF

variable {Key Dom Cod : ℕ → Type*}
variable [∀ n, Fintype (Key n)] [∀ n, Nonempty (Key n)]
variable [∀ n, Fintype (Dom n)] [∀ n, Nonempty (Dom n)] [∀ n, DecidableEq (Dom n)]
variable [∀ n, Fintype (Cod n)] [∀ n, Nonempty (Cod n)]

/-- The “real” PRF oracle ensemble (sample a uniform key, expose the keyed function). -/
noncomputable def prfRealOracle (F : ∀ n, Key n → Dom n → Cod n) : Ensemble (fun n => Dom n → Cod n) :=
  fun n => (PMF.uniformOfFintype (Key n)).map (fun k => F n k)

/-- The “random function” oracle ensemble (uniform function `Dom n → Cod n`). -/
noncomputable def prfRandomOracle : Ensemble (fun n => Dom n → Cod n) :=
  fun n => PMF.uniformOfFintype (Dom n → Cod n)

/-- `F` is a PRF against oracle distinguishers in `D` if real and random oracles are indistinguishable. -/
def IsPRF (D : Set (OracleDistinguisher Dom Cod)) (F : ∀ n, Key n → Dom n → Cod n) : Prop :=
  Indistinguishable D (prfRealOracle (Key := Key) (Dom := Dom) (Cod := Cod) F)
    (prfRandomOracle (Dom := Dom) (Cod := Cod))

/--
PRF security against a class of *query-bounded* (interactive) oracle strategies.

This feeds strategies through `QueryBoundedOracleDistinguisher.toOracleDistinguisher`.
-/
def IsPRF_queryBounded (q : ℕ → ℕ) (D : Set (QueryBoundedOracleDistinguisher Dom Cod q))
    (F : ∀ n, Key n → Dom n → Cod n) : Prop :=
  ∀ d ∈ D,
    Negligible
      (advantageEnsemble
        (QueryBoundedOracleDistinguisher.toOracleDistinguisher (dom := Dom) (cod := Cod) (q := q) d)
        (prfRealOracle (Key := Key) (Dom := Dom) (Cod := Cod) F)
        (prfRandomOracle (Dom := Dom) (Cod := Cod)))

end PRF

/-! ## Hybrid argument inequality (finite hybrids) -/

theorem abs_sub_le_sum_range (p : ℕ → ℝ) (m : ℕ) :
    |p 0 - p m| ≤ Finset.sum (Finset.range m) (fun i => |p i - p (i + 1)|) := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      classical
      set term : ℕ → ℝ := fun i => |p i - p (i + 1)|
      have htri : |p 0 - p (m + 1)| ≤ |p 0 - p m| + term m := by
        simpa [term] using abs_sub_le (p 0) (p m) (p (m + 1))
      have hstep : |p 0 - p (m + 1)| ≤ Finset.sum (Finset.range m) term + term m := by
        calc
          |p 0 - p (m + 1)| ≤ |p 0 - p m| + term m := htri
          _ ≤ Finset.sum (Finset.range m) term + term m := by
                -- `add_le_add_left` is more convenient; commute addition to match our goal.
                simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left ih (term m)
      have hsum :
          Finset.sum (Finset.range (m + 1)) term = Finset.sum (Finset.range m) term + term m := by
        -- `range (m+1) = insert m (range m)` and `m ∉ range m`.
        -- `sum_insert` yields `term m + sum`; commute to match our RHS.
        simp [Finset.range_add_one, Finset.sum_insert, Finset.mem_range, term, add_comm]
      simpa [hsum] using hstep

end

end Crypto

end Pseudorandomness
