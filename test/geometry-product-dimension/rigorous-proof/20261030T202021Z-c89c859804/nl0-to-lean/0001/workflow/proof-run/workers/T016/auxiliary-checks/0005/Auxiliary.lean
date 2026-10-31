import Mathlib
abbrev GPEucl (k : ℕ) := EuclideanSpace ℝ (Fin k)
def GPI : Set ℝ := Set.Icc 0 1
def GPappend {k : ℕ} (x : GPEucl k) (t : ℝ) : GPEucl (k + 1) :=
  WithLp.toLp 2 (Fin.snoc (fun i => x i) t)
def GPhead {k : ℕ} (z : GPEucl (k + 1)) : GPEucl k :=
  WithLp.toLp 2 (fun i : Fin k => z i.castSucc)
def GPproduct {k : ℕ} (A : Set (GPEucl k)) : Set (GPEucl (k + 1)) :=
  {z | GPhead z ∈ A ∧ z (Fin.last k) ∈ GPI}
def GPcover {X : Type*} [PseudoEMetricSpace X]
    (A : Set X) (δ : ℝ) (U : ℕ → Set X) : Prop :=
  A ⊆ ⋃ i, U i ∧ ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ
noncomputable def GPcost {X : Type*} [PseudoEMetricSpace X]
    (s : ℝ) (U : ℕ → Set X) : ENNReal :=
  ∑' i, (Metric.ediam (U i)) ^ s
noncomputable def GPcontent {X : Type*} [PseudoEMetricSpace X]
    (s δ : ℝ) (A : Set X) : ENNReal :=
  ⨅ (U : ℕ → Set X) (_ : GPcover A δ U), GPcost s U
noncomputable def GPmass {X : Type*} [PseudoEMetricSpace X]
    (s : ℝ) (A : Set X) : ENNReal :=
  ⨆ (δ : ℝ) (_ : 0 < δ), GPcontent s δ A

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace YuiAuxiliary
set_option autoImplicit false
theorem checked (n : ℕ) (E : Set (GPEucl n)) (h_T002 : (∀ (k : ℕ) (A : Set (GPEucl k)) (s : ℝ), 0 < s →
    GPmass s A = MeasureTheory.Measure.hausdorffMeasure s A) ∧
  (∀ (A : Set ℝ) (s : ℝ), 0 < s →
    GPmass s A = MeasureTheory.Measure.hausdorffMeasure s A)) (h_T014 : dimH GPI ≤ 1 ∧ ∀ a : ℝ, 1 < a → GPmass a GPI = 0) (h_T015 : ∀ (δ : ℝ) (U : ℕ → Set ℝ), 0 < δ →
  GPcover GPI δ U → (1 : ENNReal) ≤ ∑' i, Metric.ediam (U i)) : yui_aux_type% "∀ (s δ : ℝ) (d : ENNReal), 0 < s → 0 < δ → d ≤ ENNReal.ofReal δ → (δ ^ (s - 1) * d.toReal ≤ d.toReal ^ s) → ENNReal.ofReal (δ ^ (s - 1)) * d ≤ d ^ s" := by
  intro s δ d hs hδ hd hreal
  have hdtop : d ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hd
  have hconv : ENNReal.ofReal d.toReal = d := ENNReal.ofReal_toReal hdtop
  have hpow : d ^ s = ENNReal.ofReal (d.toReal ^ s) := by
    calc
      d ^ s = (ENNReal.ofReal d.toReal) ^ s := congrArg (fun x : ENNReal => x ^ s) hconv.symm
      _ = _ := ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hs.le
  calc
    ENNReal.ofReal (δ ^ (s - 1)) * d = ENNReal.ofReal (δ ^ (s - 1) * d.toReal) := by rw [ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _), hconv]
    _ ≤ ENNReal.ofReal (d.toReal ^ s) := ENNReal.ofReal_le_ofReal hreal
    _ = d ^ s := hpow.symm
#check @checked
#print axioms checked
end YuiAuxiliary
