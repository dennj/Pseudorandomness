# The Pseudorandomness Framework

A Lean 4 formalization showing that the three classical barriers in computational complexity theory—**relativization**, **algebrization**, and **natural proofs**—can be expressed as instances of a single principle: **pseudorandomness to bounded observers**.

DOI: [10.5281/zenodo.18046525](https://doi.org/10.5281/zenodo.18046525)

**PDF**: [A Unified Formal Framework for Relativization, Algebrization, and Natural Proof Barriers via Pseudorandomness](Dennj%20Osele%20-%20A%20Unified%20Formal%20Framework%20for%20Relativization,%20Algebrization,%20and%20Natural%20Proof%20Barriers%20via%20Pseudorandomness.pdf)

**Code**: <https://github.com/dennj/Pseudorandomness>

## The Core Idea

An **observer** is any process that examines a function and produces a measurement. Observers have **bounded resources**—limited queries, polynomial degree, or polynomial time. A function is **pseudorandom** to an observer class if no observer in that class can distinguish it from a random function.

> **Bounded observers cannot see structure in pseudorandom objects.**

This principle manifests across multiple fields with different terminology but similar mathematics.

## The Main Theorem

**Theorem (Observer Barrier):** If a function *f* is pseudorandom to observer class *O*, then no *O*-bounded proof technique can both certify a complexity separation AND distinguish *f* from random.

```lean
theorem observer_barrier (O : ObserverClass n)
    (f : BoolFun n) (hPR : IsPseudorandomTo f O) :
    ∀ T : ProofTechnique n, T.isOBounded O →
    ¬(T.certifiesSeparation ∧
      ∃ obs ∈ T.observerClass, |obs.observe f - obs.randomExpectation| ≥ 1 / obs.bound)
```

This theorem, instantiated with different observer classes, captures the three classical barriers:

| Barrier            | Observer Class           | Reference                 |
| ------------------ | ------------------------ | ------------------------- |
| **Relativization** | `QueryBoundedObservers`  | Baker-Gill-Solovay (1975) |
| **Algebrization**  | `DegreeBoundedObservers` | Aaronson-Wigderson (2009) |
| **Natural Proofs** | `PolyTimeObservers`      | Razborov-Rudich (1997)    |

The barriers are definitionally equal to instantiations of the observer barrier:

```lean
example : relativization_barrier q f hPR = observer_barrier (QueryBoundedObservers n q) f hPR := rfl
example : algebrization_barrier d f hPR = observer_barrier (DegreeBoundedObservers n d) f hPR := rfl
example : natural_proofs_barrier k f hPR = observer_barrier (PolyTimeObservers n k) f hPR := rfl
```

## Observer Class Hierarchy

The observer classes form a proven hierarchy:

```
QueryBounded(q) ⊆ DegreeBounded(q+1) ⊆ PolyTime(d+1)
```

**Important consequence**: Natural proofs is the strongest barrier—it subsumes relativization and algebrization. Any technique blocked by natural proofs is also blocked by the weaker barriers, but not vice versa.

## What This Framework Provides

1. **Uniform presentation**: All three barriers expressed in the same language
2. **Formal hierarchy**: Machine-verified proof that QueryBounded ⊆ DegreeBounded ⊆ PolyTime
3. **Cross-domain connections**: The same mathematical structure appears in control theory (observability) and learning theory
4. **Machine verification**: All results checked by the Lean proof assistant

## Scope and Limitations

**What this is**:
- A formalization that reframes known barriers in observer/pseudorandomness language
- A machine-verified proof of the barrier hierarchy
- A demonstration that relativization and algebrization (not originally framed as pseudorandomness) fit the same pattern as natural proofs

**What this is not**:
- A new barrier result
- A path to proving P ≠ NP
- The claim that the barriers are "unified" is primarily notational—natural proofs already subsumes the others

**Key assumption**: Like Razborov-Rudich, our results are conditional on pseudorandom functions existing against the relevant observer class.

## Interpretations Across Fields

### Complexity Theory

The three classical barriers say: if you can only analyze functions using q queries (relativization), degree-d polynomials (algebrization), or poly-time computation (natural proofs), then pseudorandom functions block your proof technique.

### Machine Learning

A hypothesis class is a bounded observer. If a target function is pseudorandom to that class, no learner from that class can distinguish it from noise. The Carmosino et al. (2016) equivalence—natural proofs exist against C iff C is PAC-learnable—reflects that both reduce to "distinguishing from random."

Note: `Applications/CarmosinoEquivalence.lean` captures the *existential* equivalence, not the constructive algorithm from the original paper.

### Control Theory

**Formalized in** `Applications/ControlTheoryBridge.lean`:

> A linear system is **observable** iff no non-zero state is **pseudorandom** to output observers.

This connects Kalman's observability theory to pseudorandomness: unobservable states are precisely those indistinguishable from zero by output measurements.

### Number Theory (Conjectural)

The Möbius function μ(n) is conjectured to be pseudorandom to bounded observers (Sarnak's conjecture, Chowla's conjecture). If true, bounded-complexity methods cannot detect structure in the primes.

⚠️ Unlike the complexity barriers, these are **open conjectures**.

## Historical Background

### Relativization (1975)

Baker-Gill-Solovay showed oracles exist relative to which P = NP and P ≠ NP. Originally framed in terms of oracle access, not pseudorandomness.

**Our reframing**: Relativizing proofs use only query-bounded observers.

### Natural Proofs (1997)

Razborov-Rudich showed that "natural" circuit lower bound proofs—those using efficiently checkable properties satisfied by many functions—cannot work if pseudorandom functions exist.

**Our reframing**: Natural proofs *already* uses pseudorandomness language. Our observer barrier for PolyTime is essentially a rephrasing of their result.

### Algebrization (2009)

Aaronson-Wigderson showed that arithmetization-style proofs cannot resolve major open problems. Originally framed in terms of low-degree extensions.

**Our reframing**: Algebrizing proofs use degree-bounded observers.

## Project Structure

```
Pseudorandomness/
├── Core/                        # The framework
│   ├── ObserverBarrier.lean     # Main theorem
│   └── ProofTechnique.lean      # Abstract proof technique structure
├── Foundations/                 # Mathematical foundations
│   └── BooleanFunction.lean     # BoundedObserver, hierarchy proofs
├── ObserverClasses/             # Observer class definitions
│   ├── QueryBounded.lean        # q-query observers
│   ├── DegreeBounded.lean       # degree-d polynomial observers
│   ├── PolyTime.lean            # polynomial-time observers
│   └── Hierarchy.lean           # Proven containment relations
├── BarrierInstances/            # Classical barriers as corollaries
│   ├── Relativization.lean      # BGS 1975
│   ├── Algebrization.lean       # AW 2009
│   └── NaturalProofs.lean       # RR 1997
├── Applications/
│   ├── PvsNP.lean               # Implications for P vs NP
│   ├── CarmosinoEquivalence.lean # Natural Proofs ↔ Learning
│   └── ControlTheoryBridge.lean  # Observability connection
└── Examples/                    # Illustrative examples (use axioms)
```

## Key Theorems

| Theorem                        | Location                                | Description               |
| ------------------------------ | --------------------------------------- | ------------------------- |
| `observer_barrier`             | `Core/ObserverBarrier.lean`             | The main theorem          |
| `relativization_barrier`       | `BarrierInstances/Relativization.lean`  | Query-bounded instance    |
| `algebrization_barrier`        | `BarrierInstances/Algebrization.lean`   | Degree-bounded instance   |
| `natural_proofs_barrier`       | `BarrierInstances/NaturalProofs.lean`   | Poly-time instance        |
| `natural_is_strongest_barrier` | `BarrierInstances/NaturalProofs.lean`   | Hierarchy theorem         |
| `observability_bridge`         | `Applications/ControlTheoryBridge.lean` | Control theory connection |

## Building

Requires Lean 4 and Mathlib.

```bash
lake build
```

## What This Means for P vs NP

The barriers explain why certain proof techniques fail:

1. **Relativization** blocks oracle-based arguments
2. **Algebrization** blocks arithmetization-style arguments
3. **Natural proofs** blocks efficient circuit analysis (if PRFs exist)

Since natural proofs subsumes the others, a proof of P ≠ NP must be **non-natural**: either non-constructive or applicable to very few functions.

This is a restatement of Razborov-Rudich's conclusion, not a new result.

## References

**Classical Barriers:**
- T. Baker, J. Gill, R. Solovay. "Relativizations of the P =? NP Question." *SIAM J. Comput.* 4(4):431-442, 1975.
- A. Razborov, S. Rudich. "Natural Proofs." *J. Comput. Syst. Sci.* 55(1):24-35, 1997.
- S. Aaronson, A. Wigderson. "Algebrization: A New Barrier in Complexity Theory." *ACM Trans. Comput. Theory* 1(1):2, 2009.

**Related Work:**
- R. Impagliazzo, V. Kabanets, A. Kolokolova. "An Axiomatic Approach to Algebrization." *STOC* 2009.
- E. Aydınlıoğlu, E. Bach. "Affine Relativization." *ECCC* TR17-111, 2017.

**Learning Connection:**
- M. Carmosino, R. Impagliazzo, V. Kabanets, A. Kolokolova. "Learning Algorithms from Natural Proofs." *CCC* 2016.

**Control Theory:**
- R.E. Kalman. "Mathematical Description of Linear Dynamical Systems." *SIAM J. Control* 1(2):152-192, 1963.

## License

MIT
