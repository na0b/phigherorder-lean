import PHigherOrder.Preamble

/-- The Iwaniec-Manfredi optimal regularity order
`s p = (7 + 1/(p-1) + sqrt (1 + 14/(p-1) + 1/(p-1)^2)) / 6`. -/
noncomputable def SOpt (p : ℝ) : ℝ :=
  (7 + 1 / (p - 1) + Real.sqrt (1 + 14 / (p - 1) + 1 / (p - 1) ^ 2)) / 6
