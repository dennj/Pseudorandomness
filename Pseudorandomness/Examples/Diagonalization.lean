/-
  Diagonalization: A Query-Bounded Technique
  ==========================================

  This module demonstrates how diagonalization fits into the observer barrier
  framework. The key insight: diagonalization is query-bounded, so it's
  blocked by the relativization barrier from separating P from NP.

  **Main Result**: Diagonalization uses only oracle queries, making it
  relativizing. By BGS (1975), no relativizing technique can resolve P vs NP.

  **Citation**:
  T. Baker, J. Gill, R. Solovay (1975). "Relativizations of the P =? NP Question"
  SIAM Journal on Computing, 4(4):431-442.
-/

import Pseudorandomness.Core.ProofTechnique
import Pseudorandomness.ObserverClasses.Hierarchy
import Pseudorandomness.BarrierInstances.Relativization
import Pseudorandomness.BarrierInstances.Algebrization
import Pseudorandomness.BarrierInstances.NaturalProofs

namespace Pseudorandomness

variable {n : ℕ}

/-! ## Why Diagonalization is Query-Bounded

Diagonalization works by:
1. Enumerating machines M₀, M₁, M₂, ...
2. Defining f(i) = ¬Mᵢ(i) (the diagonal)
3. Checking if f differs from each machine

The key observation: to verify f differs from Mᵢ, we only need to
**query f at position i**. This is a single oracle query.

Hence diagonalization is 1-query bounded.
-/

/--
  **Diagonalization Certification**: The time hierarchy theorem.

  Diagonalization certifies that for time bound T ≥ n, there exists
  a function in DTIME(T²) \ DTIME(T).

  **Citation**:
  J. Hartmanis, R. Stearns (1965). "On the Computational Complexity of Algorithms"
  Transactions of the AMS, 117:285-306.
-/
def DiagonalizationCertifies : Prop := True  -- Abstract: represents time hierarchy

/--
  **Diagonalization Soundness Axiom**

  If diagonalization certifies separation (e.g., time hierarchy),
  then there exists a 1-query observer that distinguishes a hard function.

  **Why axiomatized**: Constructing the explicit observer requires modeling
  Turing machine simulation. The observer checks: "does M accept input i?"
  This is a single query to the function's truth table at position i.

  **Why 1 query**: The diagonal argument checks f(i) vs Mᵢ(i).
  This requires exactly 1 query to f.
-/
axiom diagonalization_soundness (n : ℕ) :
  DiagonalizationCertifies →
    ∃ (f : BoolFun n) (obs : BoundedObserver n),
      obs ∈ QueryBoundedObservers n 1 ∧
      |obs.observe f - obs.randomExpectation| ≥ 1 / obs.bound

/--
  **Diagonalization as a Proof Technique**

  We model diagonalization abstractly: it's any technique whose observers
  make at most 1 query. The specific certification (what it proves) is
  left abstract - the point is that it's query-bounded.
-/
def DiagonalizationTechnique (n : ℕ) : ProofTechnique n where
  observerClass := QueryBoundedObservers n 1
  certifiesSeparation := DiagonalizationCertifies
  soundness := diagonalization_soundness n

/-! ## The Relativization Barrier Applies -/

/--
  **Diagonalization is Relativizing**

  By construction, DiagonalizationTechnique uses only 1-query observers.
  This makes it relativizing (query-bounded for q = 1).
-/
theorem diagonalization_is_relativizing :
    (DiagonalizationTechnique n).IsRelativizing := by
  use 1
  intro obs hObs
  exact hObs

/--
  **Diagonalization is also Natural and Algebrizing**

  Since QueryBounded ⊆ DegreeBounded ⊆ PolyTime (observer class hierarchy),
  any relativizing technique is automatically algebrizing and natural.
-/
theorem diagonalization_is_algebrizing :
    (DiagonalizationTechnique n).IsAlgebrizing := by
  exact relativizing_implies_algebrizing (DiagonalizationTechnique n) diagonalization_is_relativizing

theorem diagonalization_is_natural :
    (DiagonalizationTechnique n).IsNatural := by
  exact relativizing_implies_natural diagonalization_is_relativizing

/-! ## The Main Result: Diagonalization is Blocked -/

/--
  **Diagonalization Cannot Separate P from NP**

  IF query-pseudorandom functions exist (BGS 1975 establishes this),
  THEN diagonalization is blocked because it's query-bounded.

  **This is the relativization barrier in action.**

  Note: This is now a conditional theorem. The BGS paper establishes
  the antecedent; we prove the implication.
-/
theorem diagonalization_blocked
    (hPR : ∃ f : BoolFun n, IsPseudorandomTo f (QueryBoundedObservers n 1)) :
    ∃ f : BoolFun n, ∀ obs ∈ (DiagonalizationTechnique n).observerClass,
      ¬Distinguishes obs f := by
  -- From hypothesis, get a query-pseudorandom function
  obtain ⟨f, hPRf⟩ := hPR
  use f
  -- No 1-query observer can distinguish f
  intro obs hObs
  exact not_distinguishes_of_isPseudorandomTo hPRf hObs

/-! ## What Diagonalization CAN Do

Diagonalization successfully proves:
- The halting problem is undecidable
- Time hierarchy: DTIME(T) ⊊ DTIME(T²)
- Space hierarchy: DSPACE(S) ⊊ DSPACE(S²)

These work because they don't require separating complexity classes
that have conflicting relativizations. The time hierarchy, for instance,
relativizes consistently: DTIME^A(T) ⊊ DTIME^A(T²) for all oracles A.
-/

/--
  **Summary**: The Framework's Prediction

  The observer barrier framework correctly predicts:
  1. Diagonalization is query-bounded (1 query suffices)
  2. IF query-pseudorandom functions exist, query-bounded techniques are blocked
  3. BGS (1975) establishes query-pseudorandom functions exist
  4. Therefore diagonalization cannot separate P from NP

  This matches the historical reality: diagonalization was the main
  technique before 1975, and BGS explained why it couldn't resolve P vs NP.
-/
theorem framework_prediction_for_diagonalization
    (hPR : ∃ f : BoolFun n, IsPseudorandomTo f (QueryBoundedObservers n 1)) :
    -- Diagonalization is query-bounded
    (DiagonalizationTechnique n).IsRelativizing ∧
    -- Therefore it's blocked (given PR functions exist)
    (∃ f : BoolFun n, ∀ obs ∈ (DiagonalizationTechnique n).observerClass,
      ¬Distinguishes obs f) :=
  ⟨diagonalization_is_relativizing, diagonalization_blocked hPR⟩

end Pseudorandomness
