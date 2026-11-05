import PHigherOrder.Preamble

/-- The ambient plane: two-dimensional Euclidean space `R^2`, with its standard
inner product, the norm it induces, and the associated Lebesgue measure. -/
abbrev Plane : Type :=
  EuclideanSpace ℝ (Fin 2)
