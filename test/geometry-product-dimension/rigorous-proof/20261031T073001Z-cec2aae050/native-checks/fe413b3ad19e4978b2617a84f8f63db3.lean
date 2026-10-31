import Mathlib
open scoped ENNReal NNReal
namespace GP
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)
def unitInterval : Set ℝ := Set.Icc 0 1
def join {n : ℕ} (x : Space n) (t : ℝ) : Space (n + 1) :=
  WithLp.toLp 2 (Fin.snoc (fun i => x i) t)
def horizontal {n : ℕ} (z : Space (n + 1)) : Space n :=
  WithLp.toLp 2 (fun i => z i.castSucc)
def vertical {n : ℕ} (z : Space (n + 1)) : ℝ := z (Fin.last n)
def cylinder {n : ℕ} (E : Set (Space n)) : Set (Space (n + 1)) :=
  {z | horizontal z ∈ E ∧ vertical z ∈ unitInterval}
def Cover {X : Type*} [EMetricSpace X] (A : Set X) (δ : ℝ)
    (U : ℕ → Set X) : Prop :=
  A ⊆ ⋃ i, U i ∧ ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ
noncomputable def cost {X : Type*} [EMetricSpace X] (s : ℝ)
    (U : ℕ → Set X) : ℝ≥0∞ :=
  ∑' i, ⨆ (_ : (U i).Nonempty), (Metric.ediam (U i)) ^ s
noncomputable def content {X : Type*} [EMetricSpace X] (s δ : ℝ)
    (A : Set X) : ℝ≥0∞ :=
  ⨅ (U : ℕ → Set X) (_ : Cover A δ U), cost s U
noncomputable def hausdorff {X : Type*} [EMetricSpace X] (s : ℝ)
    (A : Set X) : ℝ≥0∞ :=
  ⨆ (δ : ℝ) (_ : 0 < δ), content s δ A
end GP

namespace Translation
set_option autoImplicit false

theorem T009 (n : ℕ) (E : Set (GP.Space n)) (h_T008 : ∀ (s δ : ℝ), 0 < s → 0 < δ →
  ∀ (V : ℕ → Set (GP.Space (n + 1))), GP.Cover (GP.cylinder E) δ V →
  ∀ ε : ℝ, 0 < ε →
    GP.content s δ E ≤ GP.cost (s + 1) V + ENNReal.ofReal ε) :
    ∀ (s δ : ℝ), 0 < s → 0 < δ →
  GP.content s δ E ≤ GP.content (s + 1) δ (GP.cylinder E) := by
  intro s δ hs hδ
  unfold GP.content
  refine le_iInf fun V => le_iInf fun hV => ?_
  change GP.content s δ E ≤ GP.cost (s + 1) V
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  have hεreal : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  have hconvert : ENNReal.ofReal (ε : ℝ) = (ε : ℝ≥0∞) :=
    ENNReal.ofReal_coe_nnreal
  simpa only [hconvert] using h_T008 s δ hs hδ V hV (ε : ℝ) hεreal

#check @T009
#print axioms T009

end Translation
