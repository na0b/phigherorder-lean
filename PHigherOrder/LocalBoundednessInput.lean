import PHigherOrder.IsPHarm

/-- Local boundedness for `p`-harmonic functions with integrability exponent `p`,
as a named bundle of data for `p`.  It carries a constant `Cb > 0` depending only
on `p` together with the UNIFORM bound
`|u x| ≤ Cb * ‖u‖_{L^p(B_1)}` for `x ∈ ball 0 (3/4)`,
valid for every `p`-harmonic `u` on the unit ball that lies in `L^p(B_1)`. -/
structure LocalBoundednessInput (p : ℝ) where
  Cb : ℝ
  Cb_pos : 0 < Cb
  bound : ∀ (u : Plane → ℝ) (g : Plane → Plane), IsPHarm p (Metric.ball 0 1) u g →
      MeasureTheory.MemLp u (ENNReal.ofReal p)
        (MeasureTheory.volume.restrict (Metric.ball (0 : Plane) 1)) →
      ∀ x ∈ Metric.ball (0 : Plane) (3 / 4),
        |u x| ≤ Cb * (MeasureTheory.eLpNorm u (ENNReal.ofReal p)
          (MeasureTheory.volume.restrict (Metric.ball (0 : Plane) 1))).toReal
