# The Pseudorandomness Framework

A Lean 4 formalization showing that the three classical barriers in computational complexity theory—**relativization**, **algebrization**, and **natural proofs**—can be expressed as instances of a single principle: **pseudorandomness to bounded observers**.

DOI: [10.5281/zenodo.18046525](https://doi.org/10.5281/zenodo.18046525)

**PDF**: [A Unified Formal Framework for Relativization, Algebrization, and Natural Proof Barriers via Pseudorandomness](Dennj%20Osele%20-%20A%20Unified%20Formal%20Framework%20for%20Relativization,%20Algebrization,%20and%20Natural%20Proof%20Barriers%20via%20Pseudorandomness.pdf)

**Code**: <https://github.com/dennj/Pseudorandomness>

## Repository Contents

- **Lean formalization**: `Pseudorandomness/` (library) and `Pseudorandomness.lean` (top-level entry point importing the main results and applications).
- **Paper sources**: `paper.tex`
- **Rendered PDF**: `Dennj Osele - A Unified Formal Framework for Relativization, Algebrization, and Natural Proof Barriers via Pseudorandomness.pdf`

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

### Domain Specializations

The core theorem is packaged in several convenient equivalent/robust forms in `Pseudorandomness/Core/ObserverBarrier.lean`:

- `observer_barrier_distinguisher`: same conclusion stated using `Distinguishes obs f` instead of an inequality.
- `observer_barrier_withMargin`: “slack”/approximate pseudorandomness (`IsPseudorandomToWithSlack`) blocks distinguishing with margin.
- `observer_barrier_robust`: noise-stability version using the observer-induced distance (`observerEdist`).
- `observer_barrier_onQuotient`: pushes the barrier down to the observer-kernel/quotient (when working modulo indistinguishability).

## Observer Class Hierarchy

The observer classes form a proven hierarchy:

```
QueryBounded(q) ⊆ DegreeBounded(q+1) ⊆ PolyTime(d+1)
```

**Important consequence**: Natural proofs is the strongest barrier—it subsumes relativization and algebrization. Any technique blocked by natural proofs is also blocked by the weaker barriers, but not vice versa.

## What This Framework Provides

1. **Uniform presentation**: All three barriers expressed in the same language
2. **Formal hierarchy**: Machine-verified proof that QueryBounded ⊆ DegreeBounded ⊆ PolyTime
3. **Cross-domain connections**: The same mathematical structure appears in learning (as distinguishing), control (observability/estimation), and number theory (conjectural)
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

Formalized in `Pseudorandomness/Applications/MachineLearning/MachineLearningBridge.lean`.

This repository also includes a distribution/ensemble layer (`Pseudorandomness/Foundations/MeasureCrypto.lean`) plus domain-agnostic learning-barrier and magnification lemmas:
- `Pseudorandomness/Core/LearningBarrier.lean`: indistinguishability of ensembles ⇒ negligible learner success-gap; includes `magnify` (advantage ⇒ break ⇒ consequence)
- `Pseudorandomness/Applications/MachineLearning/Magnification.lean`: ML-facing wrappers (e.g. CLWE-style reductions)
- `Pseudorandomness/Foundations/ContrastiveLearning.lean`: contrastive learning as distinguishing (positives vs product-of-marginals negatives)

### Control Theory

Formalized in:
- `Pseudorandomness/Applications/ControlTheory/ControlTheoryBridge.lean`: semantic observability ↔ injectivity of the output map
- `Pseudorandomness/Applications/ControlTheory/StochasticControlBridge.lean`: output traces as ensembles (Dirac baseline) + estimation-style barrier corollaries
- `Pseudorandomness/Applications/ControlTheory/ControlLearningBarrier.lean`: instantiation of the generic learning barrier for trace ensembles
- `Pseudorandomness/Applications/ControlTheory/ContrastiveLearning.lean`: contrastive learning on length-2 traces (positive pairs) vs shuffled negatives

This connects Kalman-style observability/identifiability to indistinguishability: if trace distributions are indistinguishable to a bounded class, then no bounded estimator can reliably separate the underlying states/parameters.

### Number Theory (Conjectural)

The Möbius function μ(n) is conjectured to be pseudorandom to bounded observers (Sarnak's conjecture, Chowla's conjecture). If true, bounded-complexity methods cannot detect structure in the primes.

Formalized in `Pseudorandomness/Applications/NumberTheory/NumberTheoryBridge.lean`.

⚠️ Unlike the complexity barriers, these are **open conjectures**, and several deep “bridge theorems” are currently stated as `axiom`s (placeholders for future mathlib formalizations).

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
├── Basic/                               # Lightweight preliminaries
│   ├── Foundations.lean                 # Basic definitions used by the core library
│   ├── ComplexityClasses.lean           # Minimal complexity class objects
│   └── Circuits.lean                    # Minimal circuit model
├── Core/                                # Core barrier framework
│   ├── Observer.lean                    # Observer primitives
│   ├── ObserverBarrier.lean             # Main theorem (complexity barriers)
│   ├── ProofTechnique.lean              # Abstract proof technique structure
│   ├── StrongProofTechnique.lean        # Stronger technique model + derived lemmas
│   ├── AxiomConsistency.lean            # Consistency notes for axiomatic bridges
│   ├── Pseudorandomness.lean            # Core namespace re-exports
│   ├── LearningBarrier.lean             # Generic learning/estimation barrier (measure-based)
│   └── (magnification lives here)       # `magnify` and related lemmas are in `Core/LearningBarrier.lean`
├── Foundations/                         # Mathematical foundations
│   ├── BooleanFunction.lean             # `BoolFun`, bounded observers, hierarchy proofs
│   ├── BooleanFunctionDistance.lean     # Observer-induced distance/quotient
│   ├── ObserverDistance.lean            # Distance/edistance utilities for observers
│   ├── Circuits.lean                    # Circuits + counting/shannon-style results
│   ├── Crypto.lean                      # Discrete (PMF) crypto layer
│   ├── MeasureCrypto.lean               # Measure/ProbabilityMeasure crypto layer (ensembles, CLWE, learning game)
│   └── ContrastiveLearning.lean         # Contrastive learning (positives vs product-of-marginals negatives)
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
│   ├── Complexity/
│   │   ├── PvsNP.lean                           # Implications for P vs NP
│   │   └── BarrierBreaking.lean                 # Additional applications
│   ├── MachineLearning/
│   │   ├── MachineLearningBridge.lean           # Carmosino-style bridge
│   │   ├── NeuralNetworks.lean                  # Minimal ReLU objects
│   │   └── Magnification.lean                   # ML-facing magnification wrappers (e.g. CLWE)
│   ├── ControlTheory/
│   │   ├── ControlTheoryBridge.lean             # Observability (semantic)
│   │   ├── StochasticControlBridge.lean         # Trace ensembles + estimation barrier corollaries
│   │   ├── ControlLearningBarrier.lean          # Instantiation of learning barrier for control
│   │   ├── Magnification.lean                   # Control-facing magnification wrappers
│   │   └── ContrastiveLearning.lean             # Contrastive learning on length-2 traces
│   └── NumberTheory/
│       └── NumberTheoryBridge.lean              # Sarnak/Chowla bridge (conjectural)
└── Examples/                    # Illustrative examples (use axioms)
```

## Key Theorems

| Theorem                        | Location                               | Description                                 |
| ------------------------------ | -------------------------------------- | ------------------------------------------- |
| `observer_barrier`             | `Core/ObserverBarrier.lean`            | The main theorem                            |
| `observer_barrier_withMargin`  | `Core/ObserverBarrier.lean`            | Approximate/slack form                      |
| `observer_barrier_robust`      | `Core/ObserverBarrier.lean`            | Noise-stability form                        |
| `observer_barrier_onQuotient`  | `Core/ObserverBarrier.lean`            | Quotient/kernel form                        |
| `relativization_barrier`       | `BarrierInstances/Relativization.lean` | Query-bounded instance                      |
| `algebrization_barrier`        | `BarrierInstances/Algebrization.lean`  | Degree-bounded instance                     |
| `natural_proofs_barrier`       | `BarrierInstances/NaturalProofs.lean`  | Poly-time instance                          |
| `natural_is_strongest_barrier` | `BarrierInstances/NaturalProofs.lean`  | Hierarchy theorem                           |
| `learning_barrier`             | `Core/LearningBarrier.lean`            | Learning/estimation barrier (distributions) |
| `magnify`                      | `Core/LearningBarrier.lean`            | Magnification template                      |

## Building

This is a Lean 4 project managed by Lake.

- Lean is pinned by `lean-toolchain` (currently `leanprover/lean4:v4.27.0-rc1`).
- Mathlib is a Lake dependency (see `lakefile.lean` and `lake-manifest.json`).

Build the library:

```bash
# Optional: download precompiled Mathlib oleans (requires network)
lake exe cache get

lake build
```

Optional (paper): build `paper.tex` with your preferred LaTeX toolchain (e.g. `latexmk -pdf paper.tex`).

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
