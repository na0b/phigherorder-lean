import PHigherOrder.Plane

/-- The Taylor polynomial of degree `k` of `u` at the point `x₀` (paper line 226, "its
Taylor polynomial `P` of degree `k` at zero"; eq:approximation, eq:coefficients, eq:small).

It is encoded through the DIAGONAL evaluations of the iterated Frechet derivatives, i.e. as
`z ↦ ∑_{j ≤ k} (1/j!) · D^j u(x₀)[z - x₀, …, z - x₀]`, which is exactly the classical formula
and is manifestly a polynomial function of degree at most `k`.  The `1/j!` coefficients are
load-bearing: they cancel the factorial produced when the `k`-th derivative of a diagonal
`k`-linear expression is computed, so the derivative identities of `TaylorPolyDeriv` come out
with no constant.

Only diagonal evaluations of `D^j u(x₀)` appear, in accordance with the standing
diagonal-evaluations-only interface of this development: Mathlib at the pinned revision has
symmetry of `iteratedFDeriv` in general order only under analyticity, which no input bundle
supplies, so the full multilinear form is never recovered from the polynomial — only its
symmetrization is, and diagonal evaluation is invariant under symmetrization. -/
noncomputable def TaylorPoly (k : ℕ) (u : Plane → ℝ) (x₀ : Plane) : Plane → ℝ :=
  fun z => ∑ j ∈ Finset.range (k + 1),
    (1 / (Nat.factorial j : ℝ)) * iteratedFDeriv ℝ j u x₀ (fun _ => z - x₀)
