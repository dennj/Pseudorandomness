/-
  Observer Class Hierarchy
  ========================

  This module re-exports and extends the PROVEN hierarchy relations
  from Pseudorandomness/Foundations:

    QueryBounded ⊆ DegreeBounded ⊆ PolyTime

  **Key Result (PROVEN in Foundations)**:
  The hierarchy is proven from the semantic constraints in BoundedObserver,
  NOT axiomatized. See Pseudorandomness/Foundations/BooleanFunction.lean for proofs.
-/

import Pseudorandomness.Core.ProofTechnique

namespace Pseudorandomness

variable {n : ℕ}

/-! ## The Hierarchy (Re-exported from Foundations)

The following relations are PROVEN in Foundations/BooleanFunction.lean:
- `query_subset_degree`: QueryBoundedObservers n q ⊆ DegreeBoundedObservers n (q + 1)
- `degree_subset_polytime`: DegreeBoundedObservers n d ⊆ PolyTimeObservers n (d + 1)
- `query_subset_polytime`: QueryBoundedObservers n q ⊆ PolyTimeObservers n (q + 2)

These follow from the semantic constraints:
- `query_degree_bound`: algebraicDegree ≤ queryComplexity + 1
- `degree_time_bound`: timeComplexity ≤ (n + 1) ^ (algebraicDegree + 1)
-/

/-! ## Implications for Pseudorandomness -/

/--
  Pseudorandomness to PolyTime(k) implies pseudorandomness to DegreeBounded(d)
  when d + 1 ≤ k.
-/
theorem polytime_pr_implies_degree_pr' {f : BoolFun n} {d k : ℕ}
    (hdk : d + 1 ≤ k)
    (hPR : IsPseudorandomTo f (PolyTimeObservers n k)) :
    IsPseudorandomTo f (DegreeBoundedObservers n d) :=
  pseudorandom_subset (ObserverClass.subset_trans (degree_subset_polytime n d)
    (PolyTime.mono hdk)) hPR

/--
  Pseudorandomness to PolyTime(k) implies pseudorandomness to QueryBounded(q)
  when q + 2 ≤ k.
-/
theorem polytime_pr_implies_query_pr' {f : BoolFun n} {q k : ℕ}
    (hqk : q + 2 ≤ k)
    (hPR : IsPseudorandomTo f (PolyTimeObservers n k)) :
    IsPseudorandomTo f (QueryBoundedObservers n q) :=
  pseudorandom_subset (ObserverClass.subset_trans (query_subset_polytime n q)
    (PolyTime.mono hqk)) hPR

/--
  Pseudorandomness to DegreeBounded(d) implies pseudorandomness to QueryBounded(q)
  when q + 1 ≤ d.
-/
theorem degree_pr_implies_query_pr' {f : BoolFun n} {q d : ℕ}
    (hqd : q + 1 ≤ d)
    (hPR : IsPseudorandomTo f (DegreeBoundedObservers n d)) :
    IsPseudorandomTo f (QueryBoundedObservers n q) :=
  pseudorandom_subset (ObserverClass.subset_trans (query_subset_degree n q)
    (DegreeBounded.mono hqd)) hPR

/-! ## Implications for Proof Techniques -/

/--
  A relativizing technique is also algebrizing (with degree bound q + 1).
-/
theorem relativizing_is_algebrizing' {T : ProofTechnique n}
    {q : ℕ} (h : T.isOBounded (QueryBoundedObservers n q)) :
    T.isOBounded (DegreeBoundedObservers n (q + 1)) :=
  ProofTechnique.isOBounded_trans h (query_subset_degree n q)

/--
  An algebrizing technique is also poly-time bounded (with exponent d + 1).
-/
theorem algebrizing_is_polytime' {T : ProofTechnique n}
    {d : ℕ} (h : T.isOBounded (DegreeBoundedObservers n d)) :
    T.isOBounded (PolyTimeObservers n (d + 1)) :=
  ProofTechnique.isOBounded_trans h (degree_subset_polytime n d)

/--
  A relativizing technique is poly-time bounded (with exponent q + 2).
-/
theorem relativizing_is_polytime' {T : ProofTechnique n}
    {q : ℕ} (h : T.isOBounded (QueryBoundedObservers n q)) :
    T.isOBounded (PolyTimeObservers n (q + 2)) :=
  ProofTechnique.isOBounded_trans h (query_subset_polytime n q)

/-! ## Implications for Barrier Instances -/

/--
  **Relativizing implies Natural** (for proof techniques)

  Any relativizing technique is also natural (bounded by PolyTime).
-/
theorem relativizing_implies_natural {T : ProofTechnique n}
    (hRel : ∃ q, T.isOBounded (QueryBoundedObservers n q)) :
    ∃ k, T.isOBounded (PolyTimeObservers n k) := by
  obtain ⟨q, hBounded⟩ := hRel
  exact ⟨q + 2, relativizing_is_polytime' hBounded⟩

/--
  **Algebrizing implies Natural** (for proof techniques)

  Any algebrizing technique is also natural (bounded by PolyTime).
-/
theorem algebrizing_implies_natural {T : ProofTechnique n}
    (hAlg : ∃ d, T.isOBounded (DegreeBoundedObservers n d)) :
    ∃ k, T.isOBounded (PolyTimeObservers n k) := by
  obtain ⟨d, hBounded⟩ := hAlg
  exact ⟨d + 1, algebrizing_is_polytime' hBounded⟩

end Pseudorandomness
