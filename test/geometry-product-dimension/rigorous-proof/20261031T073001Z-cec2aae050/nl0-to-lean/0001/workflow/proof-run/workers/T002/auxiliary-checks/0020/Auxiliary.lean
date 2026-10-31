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

open Lean Elab Term
elab "yui_aux_type% " text:str : term => do
  let parsed ← ofExcept <| Parser.runParserCategory (← getEnv) `term text.getString
  Term.elabTerm parsed none

namespace YuiAuxiliary
set_option autoImplicit false
theorem checked (n : ℕ) (E : Set (GP.Space n)) (h_H001 : 0 ≤ n) (h_H002 : E.Nonempty) (h_H003 : IsCompact E) (h_T001 : (∀ (m : ℕ) (A : Set (GP.Space m)), 0 ≤ dimH A ∧
  ∀ (s : ℝ), 0 < s →
    GP.hausdorff s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (dimH A < ENNReal.ofReal s → GP.hausdorff s A = 0) ∧
    (ENNReal.ofReal s < dimH A → GP.hausdorff s A = ⊤) ∧
    (GP.hausdorff s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GP.hausdorff s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) ∧ (∀ (A : Set ℝ) (s : ℝ), 0 < s →
    GP.hausdorff s A = MeasureTheory.Measure.hausdorffMeasure s A)) : yui_aux_type% "∀ a : ℝ, (n : ℝ) < a → GP.hausdorff a E = 0" := by
  classical
  have hfinite : ∀ {ι : Type} [Fintype ι] (s δ : ℝ) (V : ι → Set (GP.Space n)), (E ⊆ ⋃ i, V i) → (∀ i, Metric.ediam (V i) ≤ ENNReal.ofReal δ) → GP.content s δ E ≤ ∑ i, ⨆ (_ : (V i).Nonempty), (Metric.ediam (V i)) ^ s := by
    classical
    intro ι _ s δ V hV hd
    letI : Encodable ι := Encodable.ofCountable ι
    let U : ℕ → Set (GP.Space n) := fun j => ⋃ b ∈ Encodable.decode₂ ι j, V b
    have hc : GP.Cover E δ U := by
      constructor
      · simpa only [U, Encodable.iUnion_decode₂] using hV
      · intro j
        dsimp [U]
        rw [Metric.ediam_iUnion_mem_option]
        exact iSup₂_le fun b hb => hd b
    have hb : GP.content s δ E ≤ GP.cost s U := by
      unfold GP.content
      exact iInf₂_le U hc
    refine hb.trans ?_
    change (∑' j, ⨆ (_ : (U j).Nonempty), Metric.ediam (U j) ^ s) ≤ _
    rw [show (∑' j, ⨆ (_ : (U j).Nonempty), Metric.ediam (U j) ^ s) = ∑' i, ⨆ (_ : (V i).Nonempty), Metric.ediam (V i) ^ s from tsum_iUnion_decode₂ (fun A : Set (GP.Space n) => ⨆ (_ : A.Nonempty), Metric.ediam A ^ s) (by simp) V]
    rw [tsum_fintype]
  have hgrid : ∀ (b : ℝ), 0 < b → (∀ x ∈ E, ∀ i : Fin n, -b < x i ∧ x i < b) → ∀ k : ℕ, 0 < k → ∃ V : (Fin n → Fin k) → Set (GP.Space n), E ⊆ ⋃ f, V f ∧ ∀ f, Metric.ediam (V f) ≤ ENNReal.ofReal (Real.sqrt (n : ℝ) * (2 * b / k)) := by
    classical
    intro b hb hbox k hk
    let h : ℝ := 2 * b / k
    have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
    have hh : 0 < h := div_pos (by linarith) hkR
    let Q : (Fin n → Fin k) → Set (Fin n → ℝ) := fun f =>
      Set.pi Set.univ fun i => Set.Icc (-b + (f i : ℝ) * h) (-b + ((f i : ℝ) + 1) * h)
    let V : (Fin n → Fin k) → Set (GP.Space n) := fun f => WithLp.toLp 2 '' Q f
    have hcov : E ⊆ ⋃ f, V f := by
      intro x hx
      have hpos : ∀ i, 0 ≤ (x i + b) / h := fun i => div_nonneg (by linarith [(hbox x hx i).1]) hh.le
      have hlt : ∀ i, (x i + b) / h < k := by
        intro i
        apply (div_lt_iff₀ hh).mpr
        have he : (k : ℝ) * h = 2 * b := by dsimp [h]; field_simp
        rw [he]
        linarith [(hbox x hx i).2]
      let f : Fin n → Fin k := fun i => ⟨⌊(x i + b) / h⌋₊, (Nat.floor_lt (hpos i)).mpr (hlt i)⟩
      apply Set.mem_iUnion.mpr
      refine ⟨f, ?_⟩
      refine ⟨WithLp.ofLp x, ?_, by simp⟩
      rw [Set.mem_univ_pi]
      intro i
      have hl : (f i : ℝ) * h ≤ x i + b :=
        (le_div_iff₀ hh).mp (Nat.floor_le (hpos i))
      have hu : x i + b < ((f i : ℝ) + 1) * h :=
        (div_lt_iff₀ hh).mp (Nat.lt_floor_add_one ((x i + b) / h))
      exact ⟨by dsimp; linarith, by dsimp; linarith⟩
    have hLip : LipschitzWith ⟨Real.sqrt (n : ℝ), Real.sqrt_nonneg _⟩
        (WithLp.toLp 2 : (Fin n → ℝ) → GP.Space n) := by
      have hL := PiLp.lipschitzWith_toLp (p := (2 : ℝ≥0∞)) (β := fun _ : Fin n => ℝ)
      have heq : ((Fintype.card (Fin n) : ℝ≥0) ^ (1 / (2 : ℝ≥0∞)).toReal) =
          (⟨Real.sqrt (n : ℝ), Real.sqrt_nonneg _⟩ : ℝ≥0) := by
        apply NNReal.eq
        simp only [NNReal.coe_rpow, NNReal.coe_natCast, Fintype.card_fin]
        norm_num
        exact (Real.sqrt_eq_rpow _).symm
      rwa [heq] at hL
    refine ⟨V, hcov, fun f => ?_⟩
    have hQ : Metric.ediam (Q f) ≤ ENNReal.ofReal h := by
      apply Metric.ediam_pi_le_of_le
      intro i
      rw [Real.ediam_Icc]
      apply ENNReal.ofReal_le_ofReal
      ring_nf
      exact le_rfl
    let L : ℝ≥0 := ⟨Real.sqrt (n : ℝ), Real.sqrt_nonneg _⟩
    have he : (L : ℝ≥0∞) = ENNReal.ofReal (Real.sqrt (n : ℝ)) := ENNReal.ofReal_coe_nnreal.symm
    calc
      Metric.ediam (V f) ≤ ENNReal.ofReal (Real.sqrt (n : ℝ)) * Metric.ediam (Q f) := by
        change LipschitzWith L _ at hLip
        simpa only [he] using hLip.ediam_image_le (Q f)
      _ ≤ ENNReal.ofReal (Real.sqrt (n : ℝ)) * ENNReal.ofReal h := mul_le_mul_left' hQ _
      _ = ENNReal.ofReal (Real.sqrt (n : ℝ) * (2 * b / k)) := (ENNReal.ofReal_mul (Real.sqrt_nonneg _)).symm
  have hcost : ∀ (K a : ℝ), 0 ≤ K → (n : ℝ) < a → (∀ k : ℕ, 0 < k → (k : ℝ≥0∞) ^ n * (ENNReal.ofReal (K / k)) ^ a = ENNReal.ofReal (K ^ a / (k : ℝ) ^ (a - n))) ∧ Filter.Tendsto (fun k : ℕ => ENNReal.ofReal (K ^ a / (k : ℝ) ^ (a - n))) Filter.atTop (nhds 0) := by
    intro K a hK ha
    have ha0 : 0 < a := lt_of_le_of_lt (Nat.cast_nonneg n) ha
    constructor
    · intro k hk
      have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
      have he : (k : ℝ) ^ n * (K / k) ^ a = K ^ a / (k : ℝ) ^ (a - n) := by
        rw [Real.div_rpow hK hkR.le, Real.rpow_sub hkR a (n : ℝ), Real.rpow_natCast]
        have hnz : (k : ℝ) ^ a ≠ 0 := (Real.rpow_pos_of_pos hkR a).ne'
        field_simp
      rw [ENNReal.ofReal_rpow_of_nonneg (div_nonneg hK hkR.le) ha0.le]
      rw [← ENNReal.ofReal_natCast k, ← ENNReal.ofReal_pow hkR.le, ← ENNReal.ofReal_mul (pow_nonneg hkR.le n), he]
    · have ht : Filter.Tendsto (fun k : ℕ => (k : ℝ) ^ (a - n)) Filter.atTop Filter.atTop :=
        (tendsto_rpow_atTop (sub_pos.mpr ha)).comp tendsto_natCast_atTop_atTop
      have hz : Filter.Tendsto (fun k : ℕ => K ^ a / (k : ℝ) ^ (a - n)) Filter.atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop ht
      simpa only [Function.comp_def, ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp hz
  obtain ⟨b, hb, hEb⟩ := h_H003.isBounded.subset_ball_lt 0 (0 : GP.Space n)
  have hbox : ∀ x ∈ E, ∀ i : Fin n, -b < x i ∧ x i < b := by
    intro x hx i
    have hi : dist (x i) 0 < b := by
      simpa using (PiLp.dist_apply_le x (0 : GP.Space n) i).trans_lt (hEb hx)
    simpa only [Real.dist_eq, sub_zero, abs_lt] using hi
  intro a ha
  have ha0 : 0 < a := lt_of_le_of_lt (Nat.cast_nonneg n) ha
  let K : ℝ := Real.sqrt (n : ℝ) * (2 * b)
  have hK : 0 ≤ K := by positivity
  obtain ⟨halg, hlim⟩ := hcost K a hK ha
  have hdiam : Filter.Tendsto (fun k : ℕ => ENNReal.ofReal (K / k)) Filter.atTop (nhds 0) := by
    have hz : Filter.Tendsto (fun k : ℕ => K / (k : ℝ)) Filter.atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp hz
  have hc0 : ∀ δ : ℝ, 0 < δ → GP.content a δ E = 0 := by
    intro δ hδ
    apply bot_unique
    apply ge_of_tendsto hlim
    filter_upwards [Filter.eventually_ge_atTop 1, hdiam.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hδ))] with k hk hd
    obtain ⟨V, hV, hVd⟩ := hgrid b hb hbox k hk
    have hd' : ∀ f, Metric.ediam (V f) ≤ ENNReal.ofReal (K / k) := by
      intro f
      simpa only [K, mul_div_assoc] using hVd f
    calc
      GP.content a δ E ≤ ∑ f, ⨆ (_ : (V f).Nonempty), Metric.ediam (V f) ^ a :=
        hfinite a δ V hV (fun f => (hd' f).trans hd.le)
      _ ≤ ∑ f : (Fin n → Fin k), ENNReal.ofReal (K / k) ^ a := by
        apply Finset.sum_le_sum
        intro f hf
        exact iSup_le fun _ => ENNReal.rpow_le_rpow (hd' f) ha0.le
      _ = (k : ℝ≥0∞) ^ n * ENNReal.ofReal (K / k) ^ a := by
        simp [Finset.sum_const, Fintype.card_fun, nsmul_eq_mul]
      _ = ENNReal.ofReal (K ^ a / (k : ℝ) ^ (a - n)) := halg k hk
  apply bot_unique
  unfold GP.hausdorff
  exact iSup₂_le fun δ hδ => le_of_eq (hc0 δ hδ)
#check @checked
#print axioms checked
end YuiAuxiliary
