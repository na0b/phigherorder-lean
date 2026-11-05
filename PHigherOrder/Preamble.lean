-- Preamble: shared imports for all tablet nodes.
-- Add specific Mathlib imports here (never `import Mathlib`).

-- Calculus: classical gradient, iterated Frechet derivatives, C^k regularity.
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

-- Real powers with real exponents (the p-flux and Holder exponents), and their
-- continuity: the p-flux `|xi|^(p-2) xi` has a scalar factor that blows up at the
-- origin for p < 2, so continuity there needs `Real.continuous_rpow_const`.
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

-- Euclidean structure on the plane.
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

-- Integration: Bochner integrals, local integrability, L^q seminorms, and the
-- dominated convergence theorem (limit passage in the weak equation).
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

-- Uniform convergence on a set (locally uniform convergence of the blow-ups), and
-- the theorem identifying the derivative of a locally uniform limit: this is what
-- lets a limit object's CLASSICAL gradient be read off as the limit of the
-- approximating gradients, with no measure theory.
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

-- The fundamental lemma of the calculus of variations: a locally integrable field
-- annihilating every test function vanishes almost everywhere.  It lives under
-- Analysis/Distribution/, not under MeasureTheory/.
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

-- Fubini's theorem for product measures and the fundamental theorem of calculus.
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

-- One-variable iterated derivatives and Taylor's theorem with Lagrange remainder:
-- the only Taylor remainder bounds in Mathlib are one-dimensional, so the
-- higher-order estimates are obtained by restricting to rays.
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Taylor

-- Behaviour of iterated Frechet derivatives under translations and dilations.
import Mathlib.Analysis.Calculus.ContDiff.Operations

-- Linear maps out of a finite-dimensional space are continuous (equivalence of
-- norms on the space of polynomials of bounded degree).
import Mathlib.Topology.Algebra.Module.FiniteDimension

-- Arzela-Ascoli on a compact base, compact exhaustions of an open set, and the
-- mean value inequality: the ingredients of the compactness step that the paper
-- compresses into "by eq:first and the Arzela-Ascoli theorem".
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Analysis.Calculus.MeanValue

-- Lebesgue measure on a finite-dimensional inner product space, its behaviour
-- under affine maps, and the measure-preserving identification of Euclidean
-- space with a product of lines.  Without `Haar.InnerProductSpace` there is no
-- `MeasureSpace (EuclideanSpace R (Fin 2))` instance and nothing mentioning
-- `volume` elaborates.
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

-- Iterated Frechet derivatives of a continuous multilinear map, and in particular
-- `ContinuousMultilinearMap.iteratedFDeriv_comp_diagonal`: the `k`-th derivative of
-- `z |-> T (z, ..., z)` is the symmetrization of `T` times `k!`.  This is the sole
-- handle behind the Taylor-polynomial layer and it is NOT transitively present
-- through the imports above.  (Despite the file name, nothing here needs analyticity.)
import Mathlib.Analysis.Analytic.IteratedFDeriv

-- Symmetry of the SECOND derivative of a finitely-smooth function, which is what
-- exhibits a directional derivative of the gradient as the gradient of a directional
-- derivative (`d_e (Du) = D (d_e u)`).  Only order two is available at this revision;
-- general order would require analyticity.
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

-- Bounds for the iterated derivatives of a COMPOSITION
-- (`norm_iteratedFDeriv_comp_le` and its within-a-set variant): the Faa di Bruno-free
-- way to control the `C^{j,kappa}` norms of a coefficient field `x |-> A(Dv x)` by those
-- of `v`, needed by the divergence-form Schauder bootstrap.
import Mathlib.Analysis.Calculus.ContDiff.Bounds
