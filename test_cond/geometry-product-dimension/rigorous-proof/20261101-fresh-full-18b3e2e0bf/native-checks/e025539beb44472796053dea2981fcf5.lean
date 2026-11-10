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

theorem yui_aux_0003 (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
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

theorem yui_aux_0004 (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
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
  (∀ z : GDVec (n + 1), ∃ (x : GDVec n) (t : ℝ), z = GDPoint x t)) : yui_aux_type% "∀ (U : Set (GDVec n)) (ρ a b : ℝ), 0 ≤ ρ → Metric.ediam U ≤ ENNReal.ofReal ρ → b - a ≤ ρ → Metric.ediam {z | ∃ x ∈ U, ∃ t ∈ Set.Icc a b, z = GDPoint x t} ≤ ENNReal.ofReal (Real.sqrt 2 * ρ)" := by
  intro U ρ a b hρ hU hab
  apply Metric.ediam_le_of_forall_dist_le
  rintro _ ⟨x, hx, t, ht, rfl⟩ _ ⟨y, hy, u, hu, rfl⟩
  have hxy : dist x y ≤ ρ := by
    have he : edist x y ≤ ENNReal.ofReal ρ := (Metric.edist_le_ediam_of_mem hx hy).trans hU
    rw [edist_dist, ENNReal.ofReal_le_ofReal_iff hρ] at he
    exact he
  have htu : |t - u| ≤ ρ := abs_le.mpr ⟨by linarith [ht.1, hu.2], by linarith [ht.2, hu.1]⟩
  rw [h_T009.1]
  have hs : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  apply (Real.sqrt_le_iff).mpr
  constructor
  · positivity
  · rw [mul_pow, hs]
    have hx2 : dist x y ^ 2 ≤ ρ ^ 2 := by gcongr
    have ht2 : |t - u| ^ 2 ≤ ρ ^ 2 := by gcongr
    linarith

theorem yui_aux_0005 (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
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
  (∀ z : GDVec (n + 1), ∃ (x : GDVec n) (t : ℝ), z = GDPoint x t)) : yui_aux_type% "∀ (q ρ : ℝ) (N : ℕ), 0 < ρ → (N : ℝ) ≤ 2 / ρ → (N : ℝ≥0∞) * (ENNReal.ofReal (Real.sqrt 2 * ρ)) ^ (q + 1) ≤ ENNReal.ofReal (2 * (Real.sqrt 2) ^ (q + 1)) * (ENNReal.ofReal ρ) ^ q" := by
  intro q ρ N hρ hN
  have hs : 0 < Real.sqrt 2 := by positivity
  have hid : (2 / ρ) * (Real.sqrt 2 * ρ) ^ (q + 1) = (2 * (Real.sqrt 2) ^ (q + 1)) * ρ ^ q := by
    rw [Real.mul_rpow hs.le hρ.le, Real.rpow_add_one (ne_of_gt hρ)]
    field_simp
    <;> ring
  have hr : (N : ℝ) * (Real.sqrt 2 * ρ) ^ (q + 1) ≤ (2 * (Real.sqrt 2) ^ (q + 1)) * ρ ^ q := by
    rw [← hid]
    exact mul_le_mul_of_nonneg_right hN (Real.rpow_nonneg (by positivity) _)
  have he := ENNReal.ofReal_le_ofReal hr
  simpa only [ENNReal.ofReal_mul (Nat.cast_nonneg N), ENNReal.ofReal_natCast, ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * (Real.sqrt 2) ^ (q + 1)), ENNReal.ofReal_rpow_of_pos (mul_pos hs hρ), ENNReal.ofReal_rpow_of_pos hρ] using he

theorem yui_aux_0006 (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
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
  (∀ z : GDVec (n + 1), ∃ (x : GDVec n) (t : ℝ), z = GDPoint x t)) : yui_aux_type% "∀ (K : Set ℕ) (N : K → ℕ) (c : K → ℝ≥0∞), (∑' p : Σ i : K, Fin (N i), c p.1) = ∑' i : K, (N i : ℝ≥0∞) * c i" := by
  intro K N c
  rw [ENNReal.tsum_sigma' (fun p : Σ i : K, Fin (N i) => c p.1)]
  apply tsum_congr
  intro i
  simp [tsum_fintype]

theorem yui_aux_0007 (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
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
  (∀ z : GDVec (n + 1), ∃ (x : GDVec n) (t : ℝ), z = GDPoint x t)) : yui_aux_type% "∀ (K : Set ℕ) (N : K → ℕ) (ρ : K → ℝ) (q : ℝ), (∑' p : Σ i : K, Fin (N i), (ENNReal.ofReal (Real.sqrt 2 * ρ p.1)) ^ (q + 1)) = ∑' i : K, (N i : ℝ≥0∞) * (ENNReal.ofReal (Real.sqrt 2 * ρ i)) ^ (q + 1)" := by
  intro K N ρ q
  exact @yui_aux_0006 n E h_T002 h_T004 h_T007 h_T008 h_T009 K N (fun i : K => (ENNReal.ofReal (Real.sqrt 2 * ρ i)) ^ (q + 1))

theorem yui_aux_0008 (n : ℕ) (E : Set (GDVec n)) (h_T002 : ∀ (m : ℕ) (A : Set (GDVec m)),
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
  (∀ z : GDVec (n + 1), ∃ (x : GDVec n) (t : ℝ), z = GDPoint x t)) : yui_aux_type% "∀ q δ r ε : ℝ, 0 < q → 0 < δ → 0 < r → r ≤ 1 → Real.sqrt 2 * r ≤ δ → GDPositiveCover E q r ε → GDContent (q + 1) δ (GDProduct E) < ENNReal.ofReal (2 * (Real.sqrt 2) ^ (q + 1)) * ENNReal.ofReal ε" := by
  intro q δ r ε hq hδ hr hr1 hscale hcover
  classical
  obtain ⟨K, U, hU, hUd, hsum⟩ := hcover
  let ρ : K → ℝ := fun i => (Metric.ediam (U i)).toReal
  have hfin (i : K) : Metric.ediam (U i) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hUd i).2.2
  have hρpos (i : K) : 0 < ρ i :=
    ENNReal.toReal_pos_iff.mpr ⟨(hUd i).2.1, lt_top_iff_ne_top.mpr (hfin i)⟩
  have hρle (i : K) : ρ i ≤ r :=
    ENNReal.toReal_le_of_le_ofReal hr.le (hUd i).2.2
  have hρeq (i : K) : ENNReal.ofReal (ρ i) = Metric.ediam (U i) :=
    ENNReal.ofReal_toReal (hfin i)
  have hparts (i : K) := @yui_aux_0003 n E h_T002 h_T004 h_T007 h_T008 h_T009 (ρ i) (hρpos i) ((hρle i).trans hr1)
  choose N hNp hNl hNc hNcov using hparts
  let V : (Σ i : K, Fin (N i)) → Set (GDVec (n + 1)) := fun p =>
    {z | ∃ x ∈ U p.1, ∃ t ∈ Set.Icc ((p.2 : ℕ) / (N p.1 : ℝ)) (((p.2 : ℕ) + 1) / (N p.1 : ℝ)), z = GDPoint x t}
  have hV : GDProduct E ⊆ ⋃ p, V p := by
    rintro z ⟨x, hx, t, ht, rfl⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hU hx)
    obtain ⟨j, hj⟩ := hNcov i t ht
    exact Set.mem_iUnion.mpr ⟨⟨i, j⟩, x, hi, t, hj, rfl⟩
  have hdV (p : Σ i : K, Fin (N i)) :
      Metric.ediam (V p) ≤ ENNReal.ofReal (Real.sqrt 2 * ρ p.1) := by
    apply @yui_aux_0004 n E h_T002 h_T004 h_T007 h_T008 h_T009
      (U p.1) (ρ p.1) _ _ (hρpos p.1).le
    · exact (hρeq p.1).ge
    · calc
        ((p.2 : ℕ) + 1) / (N p.1 : ℝ) - (p.2 : ℕ) / (N p.1 : ℝ) = 1 / (N p.1 : ℝ) := by ring
        _ ≤ ρ p.1 := hNl p.1
  have hdδ (p : Σ i : K, Fin (N i)) : Metric.ediam (V p) ≤ ENNReal.ofReal δ := by
    apply (hdV p).trans
    apply ENNReal.ofReal_le_ofReal
    exact (mul_le_mul_of_nonneg_left (hρle p.1) (Real.sqrt_nonneg 2)).trans hscale
  have hcost (p : Σ i : K, Fin (N i)) :
      GDCost (q + 1) (V p) ≤ (ENNReal.ofReal (Real.sqrt 2 * ρ p.1)) ^ (q + 1) := by
    unfold GDCost
    exact iSup_le fun _ => ENNReal.rpow_le_rpow (hdV p) (by linarith)
  have htotal : (∑' p, GDCost (q + 1) (V p)) ≤
      ENNReal.ofReal (2 * (Real.sqrt 2) ^ (q + 1)) * ∑' i, (Metric.ediam (U i)) ^ q := by
    calc
      (∑' p, GDCost (q + 1) (V p)) ≤ ∑' p : Σ i : K, Fin (N i), (ENNReal.ofReal (Real.sqrt 2 * ρ p.1)) ^ (q + 1) :=
        ENNReal.tsum_le_tsum hcost
      _ = ∑' i : K, (N i : ℝ≥0∞) * (ENNReal.ofReal (Real.sqrt 2 * ρ i)) ^ (q + 1) := @yui_aux_0007 n E h_T002 h_T004 h_T007 h_T008 h_T009 K N ρ q
      _ ≤ ∑' i : K, ENNReal.ofReal (2 * (Real.sqrt 2) ^ (q + 1)) * (Metric.ediam (U i)) ^ q := by
        apply ENNReal.tsum_le_tsum
        intro i
        rw [← hρeq i]
        exact @yui_aux_0005 n E h_T002 h_T004 h_T007 h_T008 h_T009 q (ρ i) (N i) (hρpos i) (hNc i)
      _ = _ := ENNReal.tsum_mul_left
  have hcpos : 0 < ENNReal.ofReal (2 * (Real.sqrt 2) ^ (q + 1)) := by positivity
  exact lt_of_le_of_lt
    ((@yui_aux_0001 n E h_T002 h_T004 h_T007 h_T008 h_T009
      (GDVec (n + 1)) _ (Σ i : K, Fin (N i)) _ (GDProduct E) (q + 1) δ V hV hdδ).trans htotal)
    (ENNReal.mul_lt_mul_right (ne_of_gt hcpos) ENNReal.ofReal_ne_top hsum)

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
  (∀ z : GDVec (n + 1), ∃ (x : GDVec n) (t : ℝ), z = GDPoint x t)) : yui_aux_type% "∀ (x : ℝ≥0∞) (C : ℝ), 0 < C → (∀ ε : ℝ, 0 < ε → x < ENNReal.ofReal C * ENNReal.ofReal ε) → x = 0" := by
  intro x C hC h
  apply le_antisymm _ zero_le
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  have hεr : (0 : ℝ) < ε := by exact_mod_cast hε
  have hh := h ((ε : ℝ) / C) (div_pos hεr hC)
  have heq : ENNReal.ofReal C * ENNReal.ofReal ((ε : ℝ) / C) = (ε : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_mul hC.le, mul_div_cancel₀ _ (ne_of_gt hC)]
    exact ENNReal.ofReal_coe_nnreal
  simpa only [zero_add, heq] using hh.le
#check @checked
#print axioms checked
end YuiAuxiliary
