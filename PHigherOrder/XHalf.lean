import PHigherOrder.Plane

/-- The closed half-ball `closedBall 0 (1/2)` of the plane, regarded as a
topological space in its own right.  This is the compact base on which the paper's
`C^1` closure is taken; by the interface decision recorded in the process memory,
the `C^1` topology on a compact base is realized as the `C^0` topology on the jet
`x ↦ (v x, D v x)`, and this is the type that jet lives on. -/
abbrev XHalf : Type :=
  ↥(Metric.closedBall (0 : Plane) (1 / 2))
