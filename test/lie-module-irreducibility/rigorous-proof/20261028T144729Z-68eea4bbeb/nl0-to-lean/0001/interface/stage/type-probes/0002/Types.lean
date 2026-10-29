import Mathlib
noncomputable section
def Probe (p : ℕ) (K : Type) [Field K] (c : CharP K p) : Prop :=
  letI : CharP K p := c
  letI : Algebra (ZMod p) K := ZMod.algebra K p
  Nonempty (K ≃ₗ[ZMod p] K)

set_option autoImplicit false
#check (fun (p : ℕ) (K : Type) [f : Field K] (c : CharP K p) => Probe p K c)
