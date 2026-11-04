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
theorem yui_aux_0001 (n : ℕ) (E : Set (GDVec n)) (h_T004 : Bornology.IsBounded E ∧
  (0 : ℝ≥0∞) ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤ ∧
  (∀ s δ : ℝ, 0 < s → 0 < δ → GDContent s δ E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0)) (h_T009 : (∀ (x y : GDVec n) (t u : ℝ),
    dist (GDPoint x t) (GDPoint y u) =
      Real.sqrt (dist x y ^ 2 + |t - u| ^ 2)) ∧
  (∀ z : GDVec (n + 1), ∃ (x : GDVec n) (t : ℝ), z = GDPoint x t)) : yui_aux_type% "∃ (p : GDVec (n + 1) → GDVec n) (q : GDVec (n + 1) → ℝ), (∀ x t, p (GDPoint x t) = x ∧ q (GDPoint x t) = t) ∧ LipschitzWith 1 p ∧ LipschitzWith 1 q" := by
  classical
    let p : GDVec (n + 1) → GDVec n := fun z => Classical.choose (h_T009.2 z)
    let q : GDVec (n + 1) → ℝ := fun z => Classical.choose (Classical.choose_spec (h_T009.2 z))
    have hd (z) : z = GDPoint (p z) (q z) := Classical.choose_spec (Classical.choose_spec (h_T009.2 z))
    have hinj {x y : GDVec n} {t u : ℝ} (h : GDPoint x t = GDPoint y u) : x = y ∧ t = u := by
      have hz : dist (GDPoint x t) (GDPoint y u) = 0 := by rw [h, dist_self]
      rw [h_T009.1] at hz
      have ha : dist x y ^ 2 + |t - u| ^ 2 = 0 :=
        (Real.sqrt_eq_zero (by positivity)).mp hz
      have hxy : dist x y = 0 := by nlinarith [sq_nonneg (dist x y), sq_nonneg |t-u|]
      have htu : t - u = 0 := by nlinarith [sq_abs (t-u), sq_nonneg (t-u), sq_nonneg (dist x y)]
      exact ⟨dist_eq_zero.mp hxy, sub_eq_zero.mp htu⟩
    refine ⟨p, q, ?_, ?_, ?_⟩
    · intro x t
      exact hinj (hd (GDPoint x t)).symm
    · apply LipschitzWith.of_dist_le_mul
      intro z w
      have h := h_T009.1 (p z) (p w) (q z) (q w)
      rw [← hd z, ← hd w] at h
      simp only [NNReal.coe_one, one_mul]
      rw [h]
      exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg |q z - q w|])
    · apply LipschitzWith.of_dist_le_mul
      intro z w
      have h := h_T009.1 (p z) (p w) (q z) (q w)
      rw [← hd z, ← hd w] at h
      simp only [NNReal.coe_one, one_mul, Real.dist_eq]
      rw [h]
      exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg (dist (p z) (p w))])

theorem yui_aux_0002 (n : ℕ) (E : Set (GDVec n)) (h_T004 : Bornology.IsBounded E ∧
  (0 : ℝ≥0∞) ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤ ∧
  (∀ s δ : ℝ, 0 < s → 0 < δ → GDContent s δ E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0)) (h_T009 : (∀ (x y : GDVec n) (t u : ℝ),
    dist (GDPoint x t) (GDPoint y u) =
      Real.sqrt (dist x y ^ 2 + |t - u| ^ 2)) ∧
  (∀ z : GDVec (n + 1), ∃ (x : GDVec n) (t : ℝ), z = GDPoint x t)) : yui_aux_type% "∀ (s δ : ℝ) (K : Set ℕ) (U : K → Set (GDVec n)) (w : K → ℝ≥0∞),\n E ⊆ ⋃ i, U i → (∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ) →\n (∀ i, GDCost s (U i) ≤ w i) → GDContent s δ E ≤ ∑' i, w i" := by
  classical
    intro s δ K U w hcov hdiam hcost
    let W : ℕ → Set (GDVec n) := fun j => if h : j ∈ K then U ⟨j,h⟩ else ∅
    have hc : E ⊆ ⋃ j, W j := by
      intro x hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov hx)
      exact Set.mem_iUnion.mpr ⟨i.val, by simpa [W, i.property] using hi⟩
    have hd : ∀ j, Metric.ediam (W j) ≤ ENNReal.ofReal δ := by
      intro j
      by_cases hj : j ∈ K
      · simpa [W, hj] using hdiam ⟨j,hj⟩
      · simp [W, hj]
    have heq : (∑' j, GDCost s (W j)) = ∑' i : K, GDCost s (U i) := by
      have hsub := tsum_subtype K (fun j => GDCost s (W j))
      have hind : K.indicator (fun j => GDCost s (W j)) = (fun j => GDCost s (W j)) := by
        funext j
        by_cases hj : j ∈ K <;> simp [Set.indicator, W, hj, GDCost]
      rw [hind] at hsub
      simpa [W] using hsub.symm
    calc
      GDContent s δ E ≤ ∑' j, GDCost s (W j) :=
        iInf_le_of_le W (iInf_le_of_le hc (iInf_le_of_le hd le_rfl))
      _ = ∑' i : K, GDCost s (U i) := heq
      _ ≤ ∑' i, w i := ENNReal.tsum_le_tsum hcost

theorem yui_aux_0003 (n : ℕ) (E : Set (GDVec n)) (h_T004 : Bornology.IsBounded E ∧
  (0 : ℝ≥0∞) ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤ ∧
  (∀ s δ : ℝ, 0 < s → 0 < δ → GDContent s δ E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0)) (h_T009 : (∀ (x y : GDVec n) (t u : ℝ),
    dist (GDPoint x t) (GDPoint y u) =
      Real.sqrt (dist x y ^ 2 + |t - u| ^ 2)) ∧
  (∀ z : GDVec (n + 1), ∃ (x : GDVec n) (t : ℝ), z = GDPoint x t)) : yui_aux_type% "∀ (B : Set ℝ) (ρ η : ℝ), B.Nonempty → 0 ≤ ρ → 0 < η →\n  Metric.ediam B ≤ ENNReal.ofReal ρ →\n  ∃ J : Set ℝ, IsOpen J ∧ B ⊆ J ∧ MeasureTheory.volume J ≤ ENNReal.ofReal (ρ + η)" := by
  classical
    intro B ρ η hB hρ hη hd
    have hb : Bornology.IsBounded B := Metric.isBounded_iff_ediam_ne_top.mpr
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hd)
    let a := sInf B
    let b := sSup B
    have hlen : b - a ≤ ρ := by
      rw [← Real.diam_eq hb]
      exact ENNReal.toReal_le_of_le_ofReal hρ hd
    refine ⟨Set.Ioo (a - η/2) (b + η/2), isOpen_Ioo, ?_, ?_⟩
    · intro x hx
      have hx' := hb.subset_Icc_sInf_sSup hx
      constructor <;> dsimp [a,b] at * <;> linarith [hx'.1,hx'.2]
    · rw [Real.volume_Ioo]
      apply ENNReal.ofReal_le_ofReal
      linarith

theorem checked (n : ℕ) (E : Set (GDVec n)) (h_T004 : Bornology.IsBounded E ∧
  (0 : ℝ≥0∞) ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧ dimH E < ⊤ ∧
  (∀ s δ : ℝ, 0 < s → 0 < δ → GDContent s δ E < ⊤) ∧
  (n = 0 → E = Set.univ ∧ dimH E = 0)) (h_T009 : (∀ (x y : GDVec n) (t u : ℝ),
    dist (GDPoint x t) (GDPoint y u) =
      Real.sqrt (dist x y ^ 2 + |t - u| ^ 2)) ∧
  (∀ z : GDVec (n + 1), ∃ (x : GDVec n) (t : ℝ), z = GDPoint x t)) : yui_aux_type% "∀ (K : Set ℕ) (a : K → ℝ) (ε : ℝ), (∀ i, 0 ≤ a i) → 0 < ε →\n ∃ η : K → ℝ, (∀ i, 0 < η i) ∧\n   (∑' i, ENNReal.ofReal (a i) * ENNReal.ofReal (η i)) ≤ ENNReal.ofReal ε" := by
  classical
    intro K a ε ha hε
    let η : K → ℝ := fun i => ε * (1/2 : ℝ) ^ (i.val + 1) / (1 + a i)
    have hη (i : K) : 0 < η i := by
      dsimp [η]
      exact div_pos (mul_pos hε (pow_pos (by norm_num) _)) (by linarith [ha i])
    refine ⟨η, hη, ?_⟩
    have hterm (i : K) : ENNReal.ofReal (a i) * ENNReal.ofReal (η i) ≤
        ENNReal.ofReal ε * (2⁻¹ : ℝ≥0∞) ^ (i.val + 1) := by
      have hr : η i * a i ≤ ε * (1/2 : ℝ) ^ (i.val + 1) := by
        dsimp [η]
        rw [div_mul_eq_mul_div]
        apply (div_le_iff₀ (by linarith [ha i])).mpr
        have hp : 0 ≤ ε * (1/2 : ℝ) ^ (i.val + 1) := by positivity
        nlinarith
      calc
        ENNReal.ofReal (a i) * ENNReal.ofReal (η i) = ENNReal.ofReal (η i * a i) := by
          rw [ENNReal.ofReal_mul (hη i).le, mul_comm]
        _ ≤ ENNReal.ofReal (ε * (1/2 : ℝ) ^ (i.val + 1)) := ENNReal.ofReal_le_ofReal hr
        _ = ENNReal.ofReal ε * (2⁻¹ : ℝ≥0∞) ^ (i.val + 1) := by
          rw [ENNReal.ofReal_mul hε.le, ENNReal.ofReal_pow (by norm_num)]
          norm_num
    calc
      (∑' i, ENNReal.ofReal (a i) * ENNReal.ofReal (η i)) ≤
          ∑' i : K, ENNReal.ofReal ε * (2⁻¹ : ℝ≥0∞) ^ (i.val + 1) :=
        ENNReal.tsum_le_tsum hterm
      _ ≤ ∑' j : ℕ, ENNReal.ofReal ε * (2⁻¹ : ℝ≥0∞) ^ (j + 1) :=
        ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective _
      _ = ENNReal.ofReal ε := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric_add_one]
        norm_num
#check @checked
#print axioms checked
end YuiAuxiliary
