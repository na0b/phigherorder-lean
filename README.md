# Higher-order estimates for p-harmonic functions in the plane, in Lean 4

This repository contains a Lean 4 formalization of Theorem 1.1 of the paper below. It is built on [Mathlib](https://github.com/leanprover-community/mathlib4).

> Juan J. Manfredi, Aelson Sobral, Eduardo V. Teixeira and José Miguel Urbano,
> *Higher-order estimates for p-harmonic functions in the plane*, manuscript, 2026.

Theorem 1.1 is the uniform interior C<sup>k,β</sup> estimate for planar p-harmonic functions with 1 < p < 2. Its range is every integer k ≥ 2 and every 0 < β < 1 with k + β < s(p), where s(p) is the Iwaniec–Manfredi exponent:

  Σ<sub>j=0</sub><sup>k</sup> ‖D<sup>j</sup>u‖<sub>L<sup>∞</sup>(B<sub>1/2</sub>)</sub> + [D<sup>k</sup>u]<sub>C<sup>0,β</sup>(B<sub>1/2</sub>)</sub> ≤ C(p, k, β) ‖u‖<sub>L<sup>p</sup>(B<sub>1</sub>)</sub>.

**Six results that the paper cites from the literature are not proved.** Each is stated precisely and taken as an explicit hypothesis of the theorem; see [Cited results](#cited-results). Everything else is proved.

The development contains no `sorry` and no axioms. The theorem depends only on the three standard axioms of Lean: `propext`, `Classical.choice` and `Quot.sound`. So the theorem reads: "the cited results imply the estimate".

<!-- TODO: remove once the authors have read the Lean statements below against the paper. -->

## Result

| Paper | Lean declaration | File |
|---|---|---|
| Theorem 1.1, estimate (1.3) | `Main` | [`PHigherOrder/Main.lean`](PHigherOrder/Main.lean) |

The intermediate results of the paper also appear, among others:

| Paper | Lean declaration |
|---|---|
| Lemma 2.1 (vanishing of the higher derivatives at a critical point) | `Rigidity` |
| Lemma 2.2 (uniform C<sup>k+1</sup> bounds at a noncritical point) | `Noncritical` |
| Lemma 2.3 (decay at one of finitely many scales) | `Scales` |
| The iteration and the approximation estimate of Section 3 | `IterationStep`, `IterationDichotomy`, `Approximation` |
| The jet bounds and the Hölder estimate of Section 3 | `JetBounds`, `HolderFromJets` |

## Definitions

| Paper | Lean | Meaning |
|---|---|---|
| ℝ² | `Plane` | `EuclideanSpace ℝ (Fin 2)` |
| \|ξ\|<sup>p−2</sup>ξ | `PFlux p ξ` | real power; `PFlux p 0 = 0` |
| s(p) | `SOpt p` | (7 + 1/(p−1) + √(1 + 14/(p−1) + 1/(p−1)²)) / 6 |
| u ∈ W<sup>1,p</sup><sub>loc</sub>(Ω) is p-harmonic | `IsPHarm p Ω u g` | see below |

`IsPHarm p Ω u g` has five parts:
- Ω is open, and u is continuous on Ω.
- g is measurable and \|g\|<sup>p</sup> is integrable on every compact K ⊆ Ω, that is, g ∈ L<sup>p</sup><sub>loc</sub>.
- g is the distributional gradient of u on Ω.
- ∫<sub>Ω</sub> ⟨\|g\|<sup>p−2</sup>g, ∇φ⟩ = 0 for every φ ∈ C<sub>c</sub><sup>∞</sup> with support in Ω.

The weak gradient g is an explicit argument.

**One difference from the paper:** `IsPHarm` asks for u to be continuous. A p-harmonic function in the paper's sense is an element of W<sup>1,p</sup><sub>loc</sub>, and it has a continuous representative. The Lean theorem is a statement about that representative.

The integrability of u (u ∈ L<sup>p</sup>(B<sub>1</sub>)) is not part of `IsPHarm`. It enters `Main` as a separate hypothesis, `MemLp`, for the restriction of Lebesgue measure to the unit ball.

## Theorem 1.1

```lean
theorem Main (p : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hLR : LewisRigidityInput p) (F : FirstOrderEstimateInput p) (hIM : IMRegularityInput p)
    (hsm : SmoothAwayFromCriticalInput p) (hS : DivFormSchauderInput)
    (hLB : LocalBoundednessInput p)
    (k : ℕ) (hk : 2 ≤ k) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hks : (k : ℝ) + β < SOpt p) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (u : Plane → ℝ) (g : Plane → Plane), IsPHarm p (Metric.ball 0 1) u g →
        MeasureTheory.MemLp u (ENNReal.ofReal p)
          (MeasureTheory.volume.restrict (Metric.ball (0 : Plane) 1)) →
        (∀ j : ℕ, j ≤ k → ∀ x ∈ Metric.ball (0 : Plane) (1 / 2), ∀ w : Plane,
            |iteratedFDeriv ℝ j u x (fun _ => w)|
              ≤ C * (MeasureTheory.eLpNorm u (ENNReal.ofReal p)
                    (MeasureTheory.volume.restrict (Metric.ball (0 : Plane) 1))).toReal
                * ‖w‖ ^ j)
          ∧ (∀ x ∈ Metric.ball (0 : Plane) (1 / 2), ∀ y ∈ Metric.ball (0 : Plane) (1 / 2),
              ∀ w : Plane,
                |iteratedFDeriv ℝ k u x (fun _ => w) - iteratedFDeriv ℝ k u y (fun _ => w)|
                  ≤ C * (MeasureTheory.eLpNorm u (ENNReal.ofReal p)
                        (MeasureTheory.volume.restrict (Metric.ball (0 : Plane) 1))).toReal
                    * ‖x - y‖ ^ β * ‖w‖ ^ k)
```

The constant C is chosen before u, so it depends only on p, k, β and on the cited inputs. Two of those inputs carry constants that depend only on p. This order of quantifiers is the uniformity that the theorem asserts.

The statement differs from (1.3) in two places. Both change the constant only by a factor that depends on k.

- **Diagonal evaluations.** The derivatives are measured through their diagonal values D<sup>j</sup>u(x)[w, …, w] for \|w\| = 1, not through the operator norm ‖D<sup>j</sup>u(x)‖. For a symmetric j-linear form, polarization shows that the two are equivalent up to a constant depending only on j.
- **Two families of bounds.** The single inequality on a sum of k + 2 terms is replaced by two families of bounds:
  - each ‖D<sup>j</sup>u‖<sub>L<sup>∞</sup>(B<sub>1/2</sub>)</sub> for j ≤ k; for j = 0 this is the L<sup>∞</sup> bound for u itself;
  - the β-Hölder seminorm of D<sup>k</sup>u on B<sub>1/2</sub>.

  The single inequality and the two families each imply the other, up to a factor k + 2.

## Cited results

The six cited results are hypotheses of `Main`. Each is a structure stated in the file of the same name. No axiom is introduced. Four of them are `Prop`s.

The other two, `FirstOrderEstimateInput` and `LocalBoundednessInput`, are bundles of data. Each carries the constants of the estimate and a proof of the estimate.

| Literature (as cited in the paper) | Lean hypothesis | Content |
|---|---|---|
| Lewis's polynomial rigidity theorem | `LewisRigidityInput p` | a homogeneous polynomial of degree m ≥ 2 that is p-harmonic on all of ℝ² vanishes |
| First-order estimates of Lewis and Tolksdorf, (1.2) | `FirstOrderEstimateInput p` | κ ∈ (0, 1) and C₀ > 0 that depend only on p, such that every p-harmonic v on B<sub>1</sub> with \|v\| ≤ 1 is C¹ on B<sub>3/4</sub> and satisfies \|∇v\| ≤ C₀ and [∇v]<sub>C<sup>0,κ</sup>(B<sub>3/4</sub>)</sub> ≤ C₀ |
| Iwaniec–Manfredi regularity | `IMRegularityInput p` | for k + β < s(p), each p-harmonic u is C<sup>k,β</sup> on some ball around each point. This is **qualitative**: the radius and the constant may depend on u |
| Smoothness where Du ≠ 0 | `SmoothAwayFromCriticalInput p` | if u is C¹ with ∇u ≠ 0 on an open set U, then u is C<sup>∞</sup> on U |
| Interior Schauder estimates for linear divergence-form equations | `DivFormSchauderInput` | C<sup>j,κ</sup> coefficients that are uniformly elliptic give C<sup>j+1,κ</sup> bounds for bounded weak solutions. The constant depends only on j, κ, the ellipticity bounds, the coefficient bound and the two radii |
| Local boundedness (Lindqvist, Lemma 3.6) | `LocalBoundednessInput p` | C<sub>b</sub> > 0 that depends only on p, with \|u\| ≤ C<sub>b</sub>‖u‖<sub>L<sup>p</sup>(B<sub>1</sub>)</sub> on B<sub>3/4</sub> |

Each hypothesis was checked during the formalization for two things: that it is not stronger than the cited result, and that it is not vacuous.

## What is and is not checked by Lean

The Lean kernel checks that `Main` follows from Mathlib, the definitions and the six hypotheses, using only the three standard axioms. Lean does **not** check:

- that the cited results hold: they are taken from the literature, as in the paper;
- that the definitions and the statement say what the paper says.

The statements were reviewed against the paper during the formalization; see [How this formalization was produced](#how-this-formalization-was-produced). Readers who rely on the result should still compare them against the paper themselves, together with the definitions they use. The definitions are listed in Section 1 of the blueprint.

## Blueprint

The directory [`blueprint/`](blueprint) contains a natural-language statement and a detailed proof for every Lean declaration. These are cross-referenced to the paper and to each other. They are collected, in dependency order, in [`blueprint/blueprint.pdf`](blueprint/blueprint.pdf) (114 pages). To rebuild it, run `pdflatex blueprint.tex` three times in that directory.

## Building and checking

Install Lean with [elan](https://github.com/leanprover/elan), then:

```sh
git clone <repository URL> phigherorder-lean
cd phigherorder-lean
lake exe cache get        # download prebuilt Mathlib
lake build
lake env lean Axioms.lean # print the axioms used by the main result
```

The project is pinned to Lean `v4.33.0` and to the Mathlib commit recorded in `lakefile.lean`. On every push, continuous integration rebuilds the project and checks the axioms.

## Layout

```
PHigherOrder.lean        root module, imports the main result
PHigherOrder/            one file per definition, lemma or theorem (75 files)
Axioms.lean              #print axioms for the main result
blueprint/blueprint.tex  natural-language companion (inputs blueprint/nodes/*.tex)
```

## How this formalization was produced

The formalization was produced with [Trellis](https://github.com/wpegden/trellis), an AI-assisted formalization pipeline. AI agents (Claude, by Anthropic) wrote the Lean proofs and the blueprint under the Trellis protocol. Each node was reviewed automatically on three counts:

- the soundness of its natural-language proof;
- its faithfulness to the paper;
- the agreement between its Lean statement and its natural-language statement.

Juan J. Manfredi chose the target and decided which cited results are carried as hypotheses. He also approved the statements at the Trellis gate. The Lean kernel checks every proof.

## Citation

Please cite the paper; see [`CITATION.cff`](CITATION.cff).

## License

Apache License 2.0, the license of Mathlib. See [`LICENSE`](LICENSE).
