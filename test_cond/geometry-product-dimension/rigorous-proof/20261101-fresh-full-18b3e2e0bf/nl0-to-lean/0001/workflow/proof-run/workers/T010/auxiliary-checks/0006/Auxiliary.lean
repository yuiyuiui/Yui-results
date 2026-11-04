import Mathlib
open scoped ENNReal NNReal BigOperators
noncomputable section

abbrev GDVec (m : ℕ) := EuclideanSpace ℝ (Fin m)

def GDLine (t : ℝ) : GDVec 1 :=
  WithLp.toLp 2 (fun _ => t)

def GDInterval : Set ℝ := Set.Icc 0 1

def GDPoint {m : ℕ} (x : GDVec m) (t : ℝ) : GDVec (m + 1) :=
  WithLp.toLp 2 (Fin.snoc (fun i => x i) t)

def GDProduct {m : ℕ} (A : Set (GDVec m)) : Set (GDVec (m + 1)) :=
  {z | ∃ x ∈ A, ∃ t ∈ GDInterval, z = GDPoint x t}

def GDCost {X : Type*} [PseudoEMetricSpace X] (s : ℝ) (A : Set X) : ℝ≥0∞ :=
  ⨆ (_ : A.Nonempty), (Metric.ediam A) ^ s

def GDContent {X : Type*} [PseudoEMetricSpace X] (s δ : ℝ) (A : Set X) : ℝ≥0∞ :=
  ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i)
    (_ : ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ),
    ∑' i, GDCost s (U i)

def GDMeasure {X : Type*} [PseudoEMetricSpace X] (s : ℝ) (A : Set X) : ℝ≥0∞ :=
  ⨆ (δ : ℝ) (_ : 0 < δ), GDContent s δ A

def GDPositiveCover {X : Type*} [PseudoEMetricSpace X]
    (A : Set X) (q r ε : ℝ) : Prop :=
  ∃ (K : Set ℕ) (U : K → Set X),
    A ⊆ ⋃ i, U i ∧
    (∀ i, (U i).Nonempty ∧ 0 < Metric.ediam (U i) ∧
      Metric.ediam (U i) ≤ ENNReal.ofReal r) ∧
    (∑' i, (Metric.ediam (U i)) ^ q) < ENNReal.ofReal ε

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace YuiAuxiliary
set_option autoImplicit false
theorem yui_aux_0001 (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T004 : Bornology.IsBounded E ∧
  (0 : ℝ≥0∞) ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤ ∧
  (∀ s δ : ℝ, 0 < s → 0 < δ → GDContent s δ E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0)) (h_T007 : dimH GDInterval = 1 ∧
  (∀ a : ℝ, 1 < a → GDMeasure a GDInterval = 0) ∧
  (∀ s δ : ℝ, 0 < s → s < 1 → 0 < δ →
    ENNReal.ofReal (δ ^ (s - 1)) ≤ GDContent s δ GDInterval) ∧
  (∀ s : ℝ, 0 < s → s < 1 → GDMeasure s GDInterval = ⊤)) (h_T008 : 1 ≤ n → ∀ q r ε : ℝ,
  dimH E < ENNReal.ofReal q → 0 < r → r ≤ 1 → 0 < ε →
  GDPositiveCover E q r ε) (h_T009 : (∀ (x y : GDVec n) (t u : ℝ),
    dist (GDPoint x t) (GDPoint y u) =
      Real.sqrt (dist x y ^ 2 + |t - u| ^ 2)) ∧
  (∀ z : GDVec (n + 1), ∃ (x : GDVec n) (t : ℝ), z = GDPoint x t)) : yui_aux_type% "∀ {X : Type} [PseudoEMetricSpace X] {ι : Type} [Countable ι] (A : Set X) (s δ : ℝ) (V : ι → Set X), A ⊆ ⋃ i, V i → (∀ i, Metric.ediam (V i) ≤ ENNReal.ofReal δ) → GDContent s δ A ≤ ∑' i, GDCost s (V i)" := by
  intro X _ ι _ A s δ V hV hd
  classical
  letI : Encodable ι := Encodable.ofCountable ι
  let W : ℕ → Set X := fun j => ⋃ b ∈ Encodable.decode₂ ι j, V b
  unfold GDContent
  refine iInf_le_of_le W (iInf_le_of_le ?_ (iInf_le_of_le ?_ ?_))
  · simpa only [W, Encodable.iUnion_decode₂] using hV
  · intro j
    dsimp [W]
    rw [Metric.ediam_iUnion_mem_option]
    exact iSup₂_le fun b _ => hd b
  · exact le_of_eq (tsum_iUnion_decode₂ (GDCost s) (by simp [GDCost]) V)

theorem yui_aux_0002 (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T004 : Bornology.IsBounded E ∧
  (0 : ℝ≥0∞) ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤ ∧
  (∀ s δ : ℝ, 0 < s → 0 < δ → GDContent s δ E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0)) (h_T007 : dimH GDInterval = 1 ∧
  (∀ a : ℝ, 1 < a → GDMeasure a GDInterval = 0) ∧
  (∀ s δ : ℝ, 0 < s → s < 1 → 0 < δ →
    ENNReal.ofReal (δ ^ (s - 1)) ≤ GDContent s δ GDInterval) ∧
  (∀ s : ℝ, 0 < s → s < 1 → GDMeasure s GDInterval = ⊤)) (h_T008 : 1 ≤ n → ∀ q r ε : ℝ,
  dimH E < ENNReal.ofReal q → 0 < r → r ≤ 1 → 0 < ε →
  GDPositiveCover E q r ε) (h_T009 : (∀ (x y : GDVec n) (t u : ℝ),
    dist (GDPoint x t) (GDPoint y u) =
      Real.sqrt (dist x y ^ 2 + |t - u| ^ 2)) ∧
  (∀ z : GDVec (n + 1), ∃ (x : GDVec n) (t : ℝ), z = GDPoint x t)) : yui_aux_type% "∀ {X Y : Type} [PseudoEMetricSpace X] [PseudoEMetricSpace Y] (f : X → Y), Isometry f → ∀ (s : ℝ) (A : Set X), GDMeasure s (f '' A) ≤ GDMeasure s A" := by
  intro X Y _ _ f hf s A
  have hc : ∀ δ : ℝ, GDContent s δ (f '' A) ≤ GDContent s δ A := by
    intro δ
    unfold GDContent
    refine le_iInf fun U => le_iInf fun hU => le_iInf fun hd => ?_
    refine iInf_le_of_le (fun i => f '' U i) (iInf_le_of_le ?_ (iInf_le_of_le ?_ ?_))
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hU hx)
      exact Set.mem_iUnion.mpr ⟨i, Set.mem_image_of_mem f hi⟩
    · simpa only [hf.ediam_image] using hd
    · apply le_of_eq
      congr 1
      funext i
      simp only [GDCost, hf.ediam_image, Set.image_nonempty]
  unfold GDMeasure
  exact iSup₂_mono fun δ _ => hc δ

theorem checked (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
  (0 : ℝ≥0∞) ≤ dimH A ∧
  ∀ s : ℝ, 0 < s →
    GDMeasure s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (ENNReal.ofReal s < dimH A → GDMeasure s A = ⊤) ∧
    (dimH A < ENNReal.ofReal s → GDMeasure s A = 0) ∧
    (GDMeasure s A < ⊤ → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GDMeasure s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) (h_T004 : Bornology.IsBounded E ∧
  (0 : ℝ≥0∞) ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤ ∧
  (∀ s δ : ℝ, 0 < s → 0 < δ → GDContent s δ E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0)) (h_T007 : dimH GDInterval = 1 ∧
  (∀ a : ℝ, 1 < a → GDMeasure a GDInterval = 0) ∧
  (∀ s δ : ℝ, 0 < s → s < 1 → 0 < δ →
    ENNReal.ofReal (δ ^ (s - 1)) ≤ GDContent s δ GDInterval) ∧
  (∀ s : ℝ, 0 < s → s < 1 → GDMeasure s GDInterval = ⊤)) (h_T008 : 1 ≤ n → ∀ q r ε : ℝ,
  dimH E < ENNReal.ofReal q → 0 < r → r ≤ 1 → 0 < ε →
  GDPositiveCover E q r ε) (h_T009 : (∀ (x y : GDVec n) (t u : ℝ),
    dist (GDPoint x t) (GDPoint y u) =
      Real.sqrt (dist x y ^ 2 + |t - u| ^ 2)) ∧
  (∀ z : GDVec (n + 1), ∃ (x : GDVec n) (t : ℝ), z = GDPoint x t)) : yui_aux_type% "∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∃ N : ℕ, 0 < N ∧ 1 / (N : ℝ) ≤ ρ ∧ (N : ℝ) ≤ 2 / ρ ∧ ∀ t ∈ GDInterval, ∃ j : Fin N, t ∈ Set.Icc ((j : ℕ) / (N : ℝ)) (((j : ℕ) + 1) / (N : ℝ))" := by
  intro ρ hρ hρ1
  let N : ℕ := ⌈1 / ρ⌉₊
  have hN : 0 < N := Nat.ceil_pos.mpr (by positivity)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hceil : 1 / ρ ≤ (N : ℝ) := Nat.le_ceil _
  have hlen : 1 / (N : ℝ) ≤ ρ := (div_le_iff₀ hNr).mpr (by nlinarith [(div_le_iff₀ hρ).mp hceil])
  refine ⟨N, hN, hlen, ?_, ?_⟩
  · have hc : (N : ℝ) < 1 / ρ + 1 := Nat.ceil_lt_add_one (by positivity)
    have hh : 1 ≤ 1 / ρ := (le_div_iff₀ hρ).mpr (by simpa using hρ1)
    calc (N : ℝ) ≤ 1 / ρ + 1 := hc.le
      _ ≤ 1 / ρ + 1 / ρ := add_le_add_right hh _
      _ = 2 / ρ := by ring
  · intro t ht
    change 0 ≤ t ∧ t ≤ 1 at ht
    by_cases ht1 : t = 1
    · refine ⟨⟨N - 1, Nat.sub_lt hN (by omega)⟩, ?_⟩
      have hncast : ((N - 1 : ℕ) : ℝ) + 1 = N := by exact_mod_cast (Nat.sub_add_cancel hN)
      dsimp
      rw [ht1]
      constructor
      · apply (div_le_iff₀ hNr).mpr
        linarith
      · rw [hncast, div_self (ne_of_gt hNr)]
    · have htlt : t < 1 := lt_of_le_of_ne ht.2 ht1
      have htn : t * N < (N : ℝ) := by nlinarith
      have htn0 : 0 ≤ t * N := mul_nonneg ht.1 hNr.le
      have hj : ⌊t * (N : ℝ)⌋₊ < N := (Nat.floor_lt htn0).mpr htn
      refine ⟨⟨⌊t * (N : ℝ)⌋₊, hj⟩, ?_⟩
      constructor
      · exact (div_le_iff₀ hNr).mpr (Nat.floor_le htn0)
      · exact (le_div_iff₀ hNr).mpr (Nat.lt_floor_add_one _).le
#check @checked
#print axioms checked
end YuiAuxiliary
