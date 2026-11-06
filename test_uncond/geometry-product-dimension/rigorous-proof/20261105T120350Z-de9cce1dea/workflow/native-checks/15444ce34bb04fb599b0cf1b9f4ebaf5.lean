import Mathlib

set_option autoImplicit false
def __probe_0 :=
  (∀ (X : Type u), X → X)
def __probe_1 :=
  ((∀ (X : Type u), X → X) → (∀ (Y : Type u), Y → Y))
