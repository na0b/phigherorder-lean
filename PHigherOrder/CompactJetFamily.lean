import PHigherOrder.XHalf
import PHigherOrder.IsPHarm

/-- The paper's compact family, realized as a set of jets.  `CompactJetFamily p` is
the closure, in the supremum metric on bounded continuous maps
`BoundedContinuousFunction XHalf (ℝ × Plane)`, of the set of jets `x ↦ (v x, gradient v x)` of functions `v`
that are `p`-harmonic on `ball 0 1` with SOME weak gradient `g`, satisfy `|v| ≤ 1`
there, and vanish at the origin.

Two features of the statement are deliberate.  The generating condition asks only for
weak `p`-harmonicity with an arbitrary `g`, exactly as the paper's set does, while the
jet carries the CLASSICAL gradient; the two are reconciled downstream rather than by
strengthening the membership condition.  And membership is characterized by the
VALUES of `z`, so no continuity or boundedness obligation enters this definition. -/
noncomputable def CompactJetFamily (p : ℝ) : Set (BoundedContinuousFunction XHalf (ℝ × Plane)) :=
  closure {z : BoundedContinuousFunction XHalf (ℝ × Plane) | ∃ (v : Plane → ℝ) (g : Plane → Plane),
    IsPHarm p (Metric.ball 0 1) v g ∧
    (∀ x ∈ Metric.ball (0 : Plane) 1, |v x| ≤ 1) ∧
    v 0 = 0 ∧
    ∀ x : XHalf, z x = (v (x : Plane), gradient v (x : Plane))}
