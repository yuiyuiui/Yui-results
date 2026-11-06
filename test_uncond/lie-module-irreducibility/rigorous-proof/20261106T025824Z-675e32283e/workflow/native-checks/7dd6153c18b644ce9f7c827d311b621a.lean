import Mathlib

namespace YuiBasisObjects

noncomputable def dividedPower {V : Type*} [AddCommGroup V] [Module ℂ V]
    (f : Module.End ℂ V) (r : ℕ) : Module.End ℂ V :=
  ((r.factorial : ℂ)⁻¹) • f ^ r

def Stable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (W : Submodule K V) (f : Module.End K V) : Prop :=
  ∀ w, w ∈ W → f w ∈ W

structure AdmissibleLattice (n : ℕ) (V : Type*) [AddCommGroup V] [Module ℂ V]
    (x y : Module.End ℂ V) where
  carrier : Submodule ℤ V
  zBasis : Module.Basis (Fin n) ℤ carrier
  cBasis : Module.Basis (Fin n) ℂ V
  coe_basis : ∀ i, (zBasis i : V) = cBasis i
  stableX : ∀ (r : ℕ) (m : V), m ∈ carrier → dividedPower x r m ∈ carrier
  stableY : ∀ (r : ℕ) (m : V), m ∈ carrier → dividedPower y r m ∈ carrier

end YuiBasisObjects

namespace YuiBasis
set_option autoImplicit false
set_option Elab.async false in
theorem B001 : ∀ (F U I : Type*) [Field F] [AddCommGroup U] [Module F U] [Fintype I] [FiniteDimensional F U] (b : I → U), LinearIndependent F b → Fintype.card I = Module.finrank F U → Submodule.span F (Set.range b) = ⊤ := by
  intro F U I _ _ _ _ _ b hb hc
  exact hb.span_eq_top_of_card_eq_finrank' hc
set_option Elab.async false in
theorem B002 : ∀ (K M : Type*) [Field K] [AddCommGroup M] [Module ℤ M] (n : ℕ) (b : Module.Basis (Fin n) ℤ M), ∃ c : Module.Basis (Fin n) K (TensorProduct ℤ K M), (∀ i, c i = TensorProduct.tmul ℤ (1 : K) (b i)) ∧ Module.finrank K (TensorProduct ℤ K M) = n := by
  intro K M _ _ _ n b
  refine ⟨b.baseChange K, ?_, ?_⟩
  · intro i
    simp
  · simpa using Module.finrank_eq_card_basis (b.baseChange K)
set_option Elab.async false in
theorem B003 : ∀ (K : Type*) [Field K] (p : ℕ) [Fact (Nat.Prime p)] [CharP K p] (r : ℕ), r < p → (r.factorial : K) ≠ 0 := by
  intro K _ p _ _ r hr
  exact ((IsUnit.natCast_factorial_iff_of_charP (A := K) p).2 hr).ne_zero
set_option Elab.async false in
theorem B004 : ∀ (n j : ℕ), j ≤ n → Nat.choose n j * j.factorial * (n - j).factorial = n.factorial := by
  intro n j hj
  exact Nat.choose_mul_factorial_mul_factorial hj
set_option Elab.async false in
theorem B005 : ∀ (K M : Type*) [Field K] [AddCommGroup M] [Module ℤ M], ∃ F : Module.End ℤ M →+* Module.End K (TensorProduct ℤ K M), ∀ (f : Module.End ℤ M) (a : K) (m : M), F f (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ a (f m) := by
  intro K M _ _ _
  let F : Module.End ℤ M →+* Module.End K (TensorProduct ℤ K M) :=
    { toFun := fun f => f.baseChange K
      map_one' := LinearMap.baseChange_one ℤ M
      map_mul' := fun f g => LinearMap.baseChange_mul f g
      map_zero' := LinearMap.baseChange_zero
      map_add' := fun f g => LinearMap.baseChange_add f g }
  refine ⟨F, ?_⟩
  intro f a m
  rfl
set_option Elab.async false in
theorem B006 : ∀ (F U I : Type*) [Field F] [AddCommGroup U] [Module F U] [Fintype I] (b : Module.Basis I F U), (∀ u, ∑ i, b.repr u i • b i = u) ∧ (∀ f g : Module.End F U, (∀ i, f (b i) = g (b i)) → f = g) := by
  intro F U I _ _ _ _ b
  refine ⟨b.sum_repr, ?_⟩
  intro f g h
  exact b.ext h

end YuiBasis

/- Trusted inspector appended after the generated proof, never a worker tool.
   Its only substitution is an array of escaped (id, selector, expected type) strings. -/
namespace NL2LeanAuditProbe
open Lean Meta Elab Command Term

private def nameOf (parts : Array String) : Name :=
  parts.foldl Name.str .anonymous

private def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quotient"

private def binderKind : BinderInfo → String
  | .default => "explicit"
  | .implicit => "implicit"
  | .strictImplicit => "strict_implicit"
  | .instImplicit => "instance"

private def showType (e : Expr) : MetaM String := do
  return (← ppExpr e).pretty

private def binderInventory (type : Expr) : MetaM Json :=
  forallTelescope type fun xs body => do
    let mut rows : Array Json := #[]
    for x in xs do
      let d ← getFVarLocalDecl x
      rows := rows.push <| Json.mkObj [
        ("name", toJson d.userName.toString), ("kind", toJson (binderKind d.binderInfo)),
        ("type", toJson (← showType d.type)), ("proof_valued", toJson (← isProp d.type))]
    return Json.mkObj [("binders", toJson rows), ("result", toJson (← showType body))]

private def record (name : Name) : MetaM Json := do
  let info ← getConstInfo name
  let env ← getEnv
  let imported := env.isImportedConst name
  let moduleName := match env.getModuleIdxFor? name with
    | some idx => (env.header.moduleNames[idx.toNat]!).toString
    | none => env.mainModule.toString
  return Json.mkObj [
    ("name", toJson name.toString), ("kind", toJson (kindOf info)),
    ("imported", toJson imported), ("module", toJson moduleName),
    ("proof_valued", toJson (← isProp info.type)),
    ("instance_declaration", toJson (isInstanceCore env name)),
    ("type", toJson (← showType info.type)),
    ("signature", ← binderInventory info.type),
    ("levels", toJson (info.levelParams.map Name.toString)),
    ("direct_constants", toJson ((info.getUsedConstantsAsSet.toArray.qsort Name.lt).map Name.toString)),
    ("axioms", toJson ((← collectAxioms name).map Name.toString))]

private def inspect (roots : Array Name) : MetaM Json := do
  let mut pending := roots
  let mut seen : NameSet := {}
  let mut rows : Array Json := #[]
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    let info ← getConstInfo name
    rows := rows.push (← record name)
    if !(← getEnv).isImportedConst name then
      pending := pending ++ info.getUsedConstantsAsSet.toArray
      if let .inductInfo value := info then
        pending := pending ++ value.ctors.toArray
  return Json.mkObj [("declarations", toJson rows), ("truncated", toJson (!pending.isEmpty))]

private def actualType (selector : String) (parts : Array String) : TermElabM Expr := do
  if selector.startsWith "decl:" then
    return (← getConstInfo (nameOf parts)).type
  if selector.startsWith "value:" then
    let .defnInfo decl ← getConstInfo (nameOf parts) | throwError "Expected a defined proposition"
    return decl.value
  if selector.startsWith "premise:" then
    let wanted := "h_" ++ (selector.drop 8).toString
    let root ← getConstInfo `AuditBExport.P
    return ← forallTelescope root.type fun xs _ => do
      let mut context : Array Expr := #[]
      for x in xs do
        let binder ← getFVarLocalDecl x
        if binder.userName.toString == wanted then
          return ← mkForallFVars context binder.type
        context := context.push x
      throwError "Missing actual root premise {wanted}"
  throwError "Unsupported selector {selector}"

/- Universe parameter names belong to each declaration's binder scope.
   Rename them bijectively, retaining repetitions and all level expressions.
   This is alpha-equivalence, not a proof of logical equivalence. -/
private def sameSignature (actual expected : Expr) : MetaM (Bool × String) := do
  if ← withoutModifyingState <| isDefEq actual expected then
    return (true, "definitional")
  let actualParams := (collectLevelParams {} actual).params.toList
  let expectedParams := (collectLevelParams {} expected).params.toList
  if actualParams.length != expectedParams.length then
    return (false, "different_universe_binders")
  let levels := (List.range actualParams.length).map fun i =>
    Level.param (Name.mkSimple ("_yuiAuditLevel" ++ toString i))
  let equal ← withoutModifyingState <| isDefEq
    (actual.instantiateLevelParams actualParams levels)
    (expected.instantiateLevelParams expectedParams levels)
  return (equal, "bijective_universe_renaming")

elab "#nl2lean_audit_probe" : command => do
  let result ← liftTermElabM <| withOptions
      (fun o => (o.setBool `pp.all true).setBool `pp.universes true) do
    let checks : Array (String × String × String × Array String) := #[("B001", "decl:YuiBasis.B001", "∀ (F U I : Type*) [Field F] [AddCommGroup U] [Module F U] [Fintype I] [FiniteDimensional F U] (b : I → U), LinearIndependent F b → Fintype.card I = Module.finrank F U → Submodule.span F (Set.range b) = ⊤", #["YuiBasis", "B001"]), ("B002", "decl:YuiBasis.B002", "∀ (K M : Type*) [Field K] [AddCommGroup M] [Module ℤ M] (n : ℕ) (b : Module.Basis (Fin n) ℤ M), ∃ c : Module.Basis (Fin n) K (TensorProduct ℤ K M), (∀ i, c i = TensorProduct.tmul ℤ (1 : K) (b i)) ∧ Module.finrank K (TensorProduct ℤ K M) = n", #["YuiBasis", "B002"]), ("B003", "decl:YuiBasis.B003", "∀ (K : Type*) [Field K] (p : ℕ) [Fact (Nat.Prime p)] [CharP K p] (r : ℕ), r < p → (r.factorial : K) ≠ 0", #["YuiBasis", "B003"]), ("B004", "decl:YuiBasis.B004", "∀ (n j : ℕ), j ≤ n → Nat.choose n j * j.factorial * (n - j).factorial = n.factorial", #["YuiBasis", "B004"]), ("B005", "decl:YuiBasis.B005", "∀ (K M : Type*) [Field K] [AddCommGroup M] [Module ℤ M], ∃ F : Module.End ℤ M →+* Module.End K (TensorProduct ℤ K M), ∀ (f : Module.End ℤ M) (a : K) (m : M), F f (TensorProduct.tmul ℤ a m) = TensorProduct.tmul ℤ a (f m)", #["YuiBasis", "B005"]), ("B006", "decl:YuiBasis.B006", "∀ (F U I : Type*) [Field F] [AddCommGroup U] [Module F U] [Fintype I] (b : Module.Basis I F U), (∀ u, ∑ i, b.repr u i • b i = u) ∧ (∀ f g : Module.End F U, (∀ i, f (b i) = g (b i)) → f = g)", #["YuiBasis", "B006"])]
    let mut comparisons : Array Json := #[]
    let mut frozenComparisons : Array Json := #[]
    let mut roots : Array Name := #[`YuiBasis.B001, `YuiBasis.B002, `YuiBasis.B003, `YuiBasis.B004, `YuiBasis.B005, `YuiBasis.B006]
    for (id, selector, expectedText, parts) in checks do
      let stx ← ofExcept <| Parser.runParserCategory (← getEnv) `term expectedText
      let expected ← Term.elabTerm stx none
      Term.synthesizeSyntheticMVarsNoPostponing
      let expected ← instantiateMVars expected
      let actual ← actualType selector parts
      let (equal, method) ← sameSignature actual expected
      let row := Json.mkObj [
        ("id", toJson id), ("selector", toJson selector),
        ("expected_type", toJson (← showType expected)),
        ("actual_type", toJson (← showType actual)), ("definitionally_equal", toJson equal),
        ("comparison_method", toJson method)]
      if id.startsWith "__frozen__" then
        frozenComparisons := frozenComparisons.push row
      else
        comparisons := comparisons.push row
      if selector.startsWith "decl:" then
        roots := roots.push (nameOf parts)
    let dependencies ← inspect roots
    return Json.mkObj [("comparisons", toJson comparisons),
      ("frozen_comparisons", toJson frozenComparisons), ("dependencies", dependencies)]
  logInfo m!"NL2LEAN_AUDIT_JSON:{result.compress}"

#nl2lean_audit_probe
end NL2LeanAuditProbe
