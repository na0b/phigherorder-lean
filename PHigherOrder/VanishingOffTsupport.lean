import PHigherOrder.Plane

/-- A real function on the plane and its classical gradient field both vanish off the
function's TOPOLOGICAL support.  For the value this is immediate from the definition of
`tsupport` as a closure; for the gradient it is not, and the point is that the complement of the
closure is OPEN, so off it the function agrees with the zero function on a whole neighbourhood
and the gradient of a locally constant function vanishes.  Vanishing off the open support alone
would not give the gradient clause.

Both clauses are stated with their quantifiers INSIDE the conjunction, over all `f` and all `x`,
so that the node has no hypotheses and no parameters and a consumer obtains the pair once and
applies it to each of its own test functions. -/
theorem VanishingOffTsupport :
    (∀ (f : Plane → ℝ) (x : Plane), x ∉ tsupport f → f x = 0)
      ∧ (∀ (f : Plane → ℝ) (x : Plane), x ∉ tsupport f → gradient f x = 0) := by
  refine ⟨fun f x hx => image_eq_zero_of_notMem_tsupport hx, ?_⟩
  intro f x hx
  have hev : f =ᶠ[nhds x] fun _ : Plane => (0 : ℝ) := notMem_tsupport_iff_eventuallyEq.mp hx
  rw [hev.gradient_eq, gradient_fun_const]
