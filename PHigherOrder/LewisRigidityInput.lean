import PHigherOrder.IsPHarm

/-- Lewis's planar polynomial rigidity theorem, as a named hypothesis on `p`.
For every `m ≥ 2` and every continuous `m`-linear form `Q` on the plane, if the
degree-`m` homogeneous polynomial `x ↦ Q[x,…,x]` is `p`-harmonic on all of the
plane (with some weak gradient `G`), then it vanishes identically. -/
structure LewisRigidityInput (p : ℝ) : Prop where
  vanish : ∀ m : ℕ, 2 ≤ m →
      ∀ (Q : ContinuousMultilinearMap ℝ (fun _ : Fin m => Plane) ℝ) (G : Plane → Plane),
        IsPHarm p Set.univ (fun x => Q fun _ => x) G →
        ∀ x : Plane, Q (fun _ => x) = 0
