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

theorem T001 (n : ℕ) (E : Set (GP.Space n))  :
    (∀ (m : ℕ) (A : Set (GP.Space m)), 0 ≤ dimH A ∧
  ∀ (s : ℝ), 0 < s →
    GP.hausdorff s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (dimH A < ENNReal.ofReal s → GP.hausdorff s A = 0) ∧
    (ENNReal.ofReal s < dimH A → GP.hausdorff s A = ⊤) ∧
    (GP.hausdorff s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GP.hausdorff s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) ∧ (∀ (A : Set ℝ) (s : ℝ), 0 < s →
    GP.hausdorff s A = MeasureTheory.Measure.hausdorffMeasure s A) := by
  have hcompare : ∀ {X : Type} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
      (s : ℝ) (A : Set X),
      GP.hausdorff s A = MeasureTheory.Measure.hausdorffMeasure s A := by
    intro X _ _ _ s A
    have hc (δ : ℝ) :
        GP.content s δ A =
          ⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i)
            (_ : ∀ i, Metric.ediam (U i) ≤ ENNReal.ofReal δ), GP.cost s U := by
      simp only [GP.content, GP.Cover, iInf_and]
    rw [MeasureTheory.Measure.hausdorffMeasure_apply]
    apply le_antisymm
    · unfold GP.hausdorff
      refine iSup₂_le fun δ hδ => ?_
      rw [hc]
      exact le_iSup₂_of_le (ENNReal.ofReal δ) (ENNReal.ofReal_pos.mpr hδ) le_rfl
    · refine iSup₂_le fun r hr => ?_
      have hb (δ : ℝ) (hδ : 0 < δ) (hdr : ENNReal.ofReal δ ≤ r) :
          (⨅ (U : ℕ → Set X) (_ : A ⊆ ⋃ i, U i)
            (_ : ∀ i, Metric.ediam (U i) ≤ r), GP.cost s U) ≤ GP.hausdorff s A := by
        apply le_trans ?_ (le_iSup₂_of_le δ hδ (le_refl (GP.content s δ A)))
        rw [hc]
        refine le_iInf fun U => le_iInf fun hU => le_iInf fun hd => ?_
        exact iInf_le_of_le U (iInf_le_of_le hU
          (iInf_le_of_le (fun i => (hd i).trans hdr) le_rfl))
      by_cases ht : r = ⊤
      · subst r
        exact hb 1 zero_lt_one le_top
      · exact hb r.toReal (ENNReal.toReal_pos_iff.mpr ⟨hr, lt_top_iff_ne_top.mpr ht⟩)
          (ENNReal.ofReal_toReal ht).le
  constructor
  · intro m A
    refine ⟨bot_le, ?_⟩
    intro s hs
    have heq := hcompare s A
    let d : ℝ≥0 := ⟨s, hs.le⟩
    have hd : (d : ℝ≥0∞) = ENNReal.ofReal s :=
      ENNReal.coe_nnreal_eq d
    refine ⟨heq, ?_, ?_, ?_, ?_⟩
    · intro h
      rw [heq]
      exact hausdorffMeasure_of_dimH_lt (d := d) (hd.symm ▸ h)
    · intro h
      rw [heq]
      exact hausdorffMeasure_of_lt_dimH (d := d) (hd.symm ▸ h)
    · intro h
      rw [← hd]
      apply dimH_le_of_hausdorffMeasure_ne_top (d := d)
      change MeasureTheory.Measure.hausdorffMeasure s A ≠ ⊤
      rw [← heq, h]
      simp
    · intro h
      rw [← hd]
      apply le_dimH_of_hausdorffMeasure_eq_top (d := d)
      exact heq.symm.trans h
  · intro A s hs
    exact hcompare s A

theorem T002 (n : ℕ) (E : Set (GP.Space n)) (h_H001 : 0 ≤ n) (h_H002 : E.Nonempty) (h_H003 : IsCompact E) (h_T001 : (∀ (m : ℕ) (A : Set (GP.Space m)), 0 ≤ dimH A ∧
  ∀ (s : ℝ), 0 < s →
    GP.hausdorff s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (dimH A < ENNReal.ofReal s → GP.hausdorff s A = 0) ∧
    (ENNReal.ofReal s < dimH A → GP.hausdorff s A = ⊤) ∧
    (GP.hausdorff s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GP.hausdorff s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) ∧ (∀ (A : Set ℝ) (s : ℝ), 0 < s →
    GP.hausdorff s A = MeasureTheory.Measure.hausdorffMeasure s A)) :
    dimH E < ⊤ ∧ 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧
  (n = 0 → E = Set.univ ∧ (∃ x : GP.Space n, E = {x}) ∧ dimH E = 0) ∧
  ∀ (s δ : ℝ), 0 < s → 0 < δ → GP.content s δ E < ⊤ := by
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
  have hzero : n = 0 → E = Set.univ ∧ (∃ x : GP.Space n, E = {x}) ∧ dimH E = 0 := by
    classical
    intro hn
    subst n
    obtain ⟨x, hx⟩ := h_H002
    have huniq : ∀ y : GP.Space 0, y = x := by
      intro y
      ext i
      exact Fin.elim0 i
    have he : E = {x} := by
      ext y
      simp only [Set.mem_singleton_iff]
      exact ⟨fun _ => huniq y, fun hy => hy ▸ hx⟩
    have hu : E = Set.univ := by
      ext y
      simp only [Set.mem_univ, iff_true]
      exact (huniq y) ▸ hx
    have hz : ∀ s : ℝ, 0 < s → GP.hausdorff s E = 0 := by
      intro s hs
      let U : ℕ → Set (GP.Space 0) := fun j => if j = 0 then {x} else ∅
      have hc : GP.cost s U = 0 := by
        unfold GP.cost
        apply ENNReal.tsum_eq_zero.mpr
        intro j
        by_cases hj : j = 0 <;> simp [U, hj, ENNReal.zero_rpow_of_pos hs]
      apply bot_unique
      unfold GP.hausdorff
      refine iSup₂_le fun δ hδ => ?_
      have hcover : GP.Cover E δ U := by
        constructor
        · intro y hy
          exact Set.mem_iUnion.mpr ⟨0, by simpa [U, he] using hy⟩
        · intro j
          by_cases hj : j = 0 <;> simp [U, hj]
      exact (iInf₂_le U hcover).trans_eq hc
    have hd : dimH E = 0 := by
      apply bot_unique
      by_contra! h
      obtain ⟨a, ha, had⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp h
      have haR : 0 < (a : ℝ) := by
        change (0 : ℝ≥0∞) < a at ha
        exact_mod_cast ha
      have hb := (h_T001.1 0 E).2 (a : ℝ) haR
      have hb' : dimH E ≤ (a : ℝ≥0∞) := by
        simpa only [ENNReal.ofReal_coe_nnreal] using hb.2.2.2.1 (hz a haR)
      exact had.not_ge hb'
    exact ⟨hu, ⟨x, he⟩, hd⟩
  have hmesh : ∀ a : ℝ, (n : ℝ) < a → GP.hausdorff a E = 0 := by
    classical
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
  have hbound : dimH E ≤ (n : ℝ≥0∞) := by
    by_cases hn : n = 0
    · simpa [hn] using le_of_eq (hzero hn).2.2
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      by_contra! h
      obtain ⟨a, ha, had⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp h
      have haR : (n : ℝ) < a := by exact_mod_cast ha
      have ha0 : 0 < (a : ℝ) := lt_of_le_of_lt (Nat.cast_nonneg n) haR
      have hb := (h_T001.1 n E).2 (a : ℝ) ha0
      have hb' : dimH E ≤ (a : ℝ≥0∞) := by
        simpa only [ENNReal.ofReal_coe_nnreal] using hb.2.2.2.1 (hmesh a haR)
      exact had.not_ge hb'
  refine ⟨lt_of_le_of_lt hbound (ENNReal.natCast_lt_top n), (h_T001.1 n E).1, hbound, hzero, ?_⟩
  intro s δ hs hδ
  obtain ⟨t, htE, ht, hcov⟩ := h_H003.finite_cover_balls (half_pos hδ)
  letI : Fintype t := ht.fintype
  let V : t → Set (GP.Space n) := fun x => Metric.ball x.1 (δ / 2)
  have hd : ∀ i, Metric.ediam (V i) ≤ ENNReal.ofReal δ := by
    intro i
    apply Metric.ediam_le_of_forall_dist_le
    intro x hx y hy
    have hx' : dist x i.1 < δ / 2 := hx
    have hy' : dist y i.1 < δ / 2 := hy
    exact (dist_triangle_right x y i.1).trans (by linarith)
  have hV : E ⊆ ⋃ i, V i := by
    intro x hx
    rcases Set.mem_iUnion₂.mp (hcov hx) with ⟨y, hy, hxy⟩
    exact Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hxy⟩
  apply lt_of_le_of_lt (hfinite s δ V hV hd)
  apply ENNReal.sum_lt_top.mpr
  intro i hi
  exact lt_of_le_of_lt (iSup_le fun _ => ENNReal.rpow_le_rpow (hd i) hs.le)
    (ENNReal.rpow_lt_top_of_nonneg hs.le ENNReal.ofReal_ne_top)

theorem T003 (n : ℕ) (E : Set (GP.Space n)) (h_T001 : (∀ (m : ℕ) (A : Set (GP.Space m)), 0 ≤ dimH A ∧
  ∀ (s : ℝ), 0 < s →
    GP.hausdorff s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (dimH A < ENNReal.ofReal s → GP.hausdorff s A = 0) ∧
    (ENNReal.ofReal s < dimH A → GP.hausdorff s A = ⊤) ∧
    (GP.hausdorff s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GP.hausdorff s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) ∧ (∀ (A : Set ℝ) (s : ℝ), 0 < s →
    GP.hausdorff s A = MeasureTheory.Measure.hausdorffMeasure s A)) :
    dimH GP.unitInterval = 1 ∧
  (∀ a : ℝ, 1 < a → GP.hausdorff a GP.unitInterval = 0) ∧
  (∀ s : ℝ, 0 < s → s < 1 → GP.hausdorff s GP.unitInterval = ⊤) := by
  classical
  have upper_native : ∀ a : ℝ, 1 < a →
      MeasureTheory.Measure.hausdorffMeasure a GP.unitInterval = 0 := by
    classical
    intro a ha
    have subdiv : ∀ (N : ℕ), 0 < N → ∀ (d x : ℝ), 0 ≤ x → x ≤ (N : ℝ) * d →
        ∃ k : ℕ, k < N ∧ (k : ℝ) * d ≤ x ∧ x ≤ ((k : ℝ) + 1) * d := by
      intro N
      induction N with
      | zero => simp
      | succ N ih =>
        intro hN d x hx hxd
        by_cases h : N = 0
        · subst N
          exact ⟨0, by omega, by simpa using hx, by simpa using hxd⟩
        · by_cases hle : x ≤ (N : ℝ) * d
          · obtain ⟨k, hk, hkx⟩ := ih (Nat.pos_of_ne_zero h) d x hx hle
            exact ⟨k, Nat.lt_succ_of_lt hk, hkx⟩
          · exact ⟨N, Nat.lt_succ_self N, (lt_of_not_ge hle).le, by exact_mod_cast hxd⟩
    let d : ℕ → ℝ := fun k => ((k + 1 : ℕ) : ℝ)⁻¹
    let t : (k : ℕ) → Fin (k + 1) → Set ℝ :=
      fun k i => Set.Icc ((i : ℝ) * d k) (((i : ℝ) + 1) * d k)
    have hd (k : ℕ) : 0 < d k := by dsimp [d]; positivity
    have hdiam (k : ℕ) (i : Fin (k+1)) :
        Metric.ediam (t k i) = ENNReal.ofReal (d k) := by
      dsimp [t]
      rw [Real.ediam_Icc]
      congr 1
      ring
    have hcover (k : ℕ) : GP.unitInterval ⊆ ⋃ i, t k i := by
      intro x hx
      obtain ⟨i, hi, hix, hxi⟩ := subdiv (k+1) (by omega) (d k) x hx.1 (by
        simpa only [d, Nat.cast_add, Nat.cast_one, mul_inv_cancel₀ (show (k : ℝ)+1 ≠ 0 by positivity)] using hx.2)
      exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hix, hxi⟩
    have hNat : Filter.Tendsto (fun k : ℕ => ((k+1 : ℕ) : ℝ)) Filter.atTop Filter.atTop :=
      tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 1)
    have hdlim : Filter.Tendsto d Filter.atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp hNat
    have hrlim : Filter.Tendsto (fun k => ENNReal.ofReal (d k)) Filter.atTop (nhds 0) := by
      simpa only [ENNReal.ofReal_zero, Function.comp_def] using
        (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hdlim
    have hcost (k : ℕ) :
        (∑ i : Fin (k+1), (Metric.ediam (t k i)) ^ a) =
          ENNReal.ofReal (((k+1 : ℕ) : ℝ) ^ (1-a)) := by
      simp_rw [hdiam]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        ENNReal.ofReal_rpow_of_pos (hd k)]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      dsimp [d]
      rw [Real.inv_rpow (by positivity), Real.rpow_sub (by positivity),
        Real.rpow_one, div_eq_mul_inv]
    have hcostlim : Filter.Tendsto
        (fun k : ℕ => ∑ i : Fin (k+1), (Metric.ediam (t k i)) ^ a)
        Filter.atTop (nhds 0) := by
      simp_rw [hcost]
      have hh : Filter.Tendsto (fun k : ℕ => ((k+1 : ℕ) : ℝ) ^ (1-a))
          Filter.atTop (nhds 0) := by
        convert (tendsto_rpow_neg_atTop (sub_pos.mpr ha)).comp hNat using 1 <;>
          simp [neg_sub, Function.comp_def]
      simpa only [ENNReal.ofReal_zero, Function.comp_def] using
        (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hh
    apply le_antisymm _ (zero_le)
    calc
      MeasureTheory.Measure.hausdorffMeasure a GP.unitInterval ≤
          Filter.liminf (fun k : ℕ => ∑ i : Fin (k+1), Metric.ediam (t k i) ^ a)
            Filter.atTop :=
        MeasureTheory.Measure.hausdorffMeasure_le_liminf_sum a GP.unitInterval
          (fun k => ENNReal.ofReal (d k)) hrlim t
          (Filter.Eventually.of_forall fun k i => (hdiam k i).le)
          (Filter.Eventually.of_forall hcover)
      _ = 0 := hcostlim.liminf_eq
  have upper : ∀ a : ℝ, 1 < a → GP.hausdorff a GP.unitInterval = 0 := by
    intro a ha
    rw [h_T001.2 GP.unitInterval a (lt_trans zero_lt_one ha)]
    exact upper_native a ha
  have lower : ∀ s : ℝ, 0 < s → s < 1 → GP.hausdorff s GP.unitInterval = ⊤ := by
    classical
    have content_lower : ∀ (s : ℝ), 0 < s → s < 1 → ∀ (δ : ℝ), 0 < δ →
        ENNReal.ofReal (δ ^ (s-1)) ≤ GP.content s δ GP.unitInterval := by
      classical
      have length : ∀ (δ : ℝ), 0 < δ → ∀ (V : ℕ → Set ℝ),
          GP.Cover GP.unitInterval δ V → (1 : ℝ≥0∞) ≤ ∑' i, Metric.ediam (V i) := by
        classical
        intro δ hδ V hV
        have hb (i : ℕ) : Bornology.IsBounded (V i) :=
          Metric.isBounded_iff_ediam_ne_top.mpr
            (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hV.2 i))
        apply ENNReal.le_of_forall_pos_le_add
        intro ε hε _
        let w : ℕ → ℝ := fun i => (ε : ℝ) / 2 / 2 ^ i
        let h : ℕ → ℝ := fun i => w i / 2
        have hw (i : ℕ) : 0 < w i := by dsimp [w]; positivity
        have hh (i : ℕ) : 0 < h i := half_pos (hw i)
        let J : ℕ → Set ℝ := fun i =>
          if (V i).Nonempty then Set.Ioo (sInf (V i) - h i) (sSup (V i) + h i) else ∅
        have hsub (i : ℕ) : V i ⊆ J i := by
          intro x hx
          have hne : (V i).Nonempty := ⟨x, hx⟩
          simp only [J, if_pos hne]
          obtain ⟨hl, hu⟩ := (hb i).subset_Icc_sInf_sSup hx
          constructor <;> linarith [hh i]
        have hopen (i : ℕ) : IsOpen (J i) := by
          dsimp [J]
          split_ifs <;> simp only [isOpen_Ioo, isOpen_empty]
        have hJ (i : ℕ) :
            MeasureTheory.volume (J i) ≤ Metric.ediam (V i) + ENNReal.ofReal (w i) := by
          by_cases hne : (V i).Nonempty
          · simp only [J, if_pos hne, Real.volume_Ioo, Real.ediam_eq (hb i)]
            calc
              ENNReal.ofReal (sSup (V i) + h i - (sInf (V i) - h i)) =
                  ENNReal.ofReal ((sSup (V i) - sInf (V i)) + w i) := by
                congr 1
                dsimp [h]
                ring
              _ ≤ _ := ENNReal.ofReal_add_le
          · simp only [J, if_neg hne, MeasureTheory.measure_empty, zero_le]
        have hcover : GP.unitInterval ⊆ ⋃ i, J i :=
          hV.1.trans (Set.iUnion_mono hsub)
        have hsum : (∑' i, ENNReal.ofReal (w i)) = (ε : ℝ≥0∞) := by
          rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => (hw i).le)
            (summable_geometric_two' (ε : ℝ))]
          simp only [w, tsum_geometric_two', ENNReal.ofReal_coe_nnreal]
        calc
          (1 : ℝ≥0∞) = MeasureTheory.volume GP.unitInterval := by
            simp [GP.unitInterval, Real.volume_Icc]
          _ ≤ MeasureTheory.volume (⋃ i, J i) := MeasureTheory.measure_mono hcover
          _ ≤ ∑' i, MeasureTheory.volume (J i) := MeasureTheory.measure_iUnion_le _
          _ ≤ ∑' i, (Metric.ediam (V i) + ENNReal.ofReal (w i)) :=
            ENNReal.tsum_le_tsum hJ
          _ = (∑' i, Metric.ediam (V i)) + ε := by rw [ENNReal.tsum_add, hsum]
      have point : ∀ (s δ r : ℝ), 0 < s → s < 1 → 0 < δ → 0 ≤ r → r ≤ δ →
          ENNReal.ofReal (δ ^ (s-1)) * ENNReal.ofReal r ≤ ENNReal.ofReal r ^ s := by
        intro s δ r hs hs1 hδ hr hrδ
        by_cases hr0 : r = 0
        · subst r
          simp [ENNReal.zero_rpow_of_pos hs]
        · have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
          rw [ENNReal.ofReal_rpow_of_nonneg hr hs.le,
            ← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _)]
          apply ENNReal.ofReal_le_ofReal
          calc
            δ ^ (s-1) * r ≤ r ^ (s-1) * r :=
              mul_le_mul_of_nonneg_right
                (Real.rpow_le_rpow_of_nonpos hrp hrδ (by linarith)) hr
            _ = r ^ s := by
              conv_rhs => rw [show s = (s-1)+1 by ring, Real.rpow_add hrp, Real.rpow_one]
      intro s hs hs1 δ hδ
      unfold GP.content
      refine le_iInf fun V => le_iInf fun hV => ?_
      have hfin (i : ℕ) : Metric.ediam (V i) ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hV.2 i)
      have hrepr (i : ℕ) :
          ENNReal.ofReal ((Metric.ediam (V i)).toReal) = Metric.ediam (V i) :=
        ENNReal.ofReal_toReal (hfin i)
      have hp (i : ℕ) :
          ENNReal.ofReal (δ ^ (s-1)) * Metric.ediam (V i) ≤
            ⨆ (_ : (V i).Nonempty), Metric.ediam (V i) ^ s := by
        by_cases hne : (V i).Nonempty
        · have H := point s δ (Metric.ediam (V i)).toReal hs hs1 hδ
            ENNReal.toReal_nonneg (ENNReal.toReal_le_of_le_ofReal hδ.le (hV.2 i))
          rw [hrepr i] at H
          exact H.trans (le_iSup (fun _ : (V i).Nonempty => Metric.ediam (V i) ^ s) hne)
        · have hempty : V i = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
          simp [hempty]
      calc
        ENNReal.ofReal (δ ^ (s-1)) = ENNReal.ofReal (δ ^ (s-1)) * 1 := (mul_one _).symm
        _ ≤ ENNReal.ofReal (δ ^ (s-1)) * ∑' i, Metric.ediam (V i) :=
          mul_le_mul_left' (length δ hδ V hV) _
        _ = ∑' i, ENNReal.ofReal (δ ^ (s-1)) * Metric.ediam (V i) :=
          ENNReal.tsum_mul_left.symm
        _ ≤ GP.cost s V := ENNReal.tsum_le_tsum hp
    intro s hs hs1
    by_contra htop
    have hbound (δ : ℝ) (hδ : 0 < δ) :
        ENNReal.ofReal (δ ^ (s-1)) ≤ GP.hausdorff s GP.unitInterval :=
      (content_lower s hs hs1 δ hδ).trans
        (le_iSup₂ (f := fun δ (_ : 0 < δ) => GP.content s δ GP.unitInterval) δ hδ)
    have he : ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0),
        (GP.hausdorff s GP.unitInterval).toReal + 1 ≤ δ ^ (s-1) :=
      (tendsto_rpow_neg_nhdsGT_zero (sub_neg.mpr hs1)).eventually
        (Filter.eventually_ge_atTop _)
    obtain ⟨δ, hlarge, hδ⟩ := (he.and self_mem_nhdsWithin).exists
    have hsmall : δ ^ (s-1) ≤ (GP.hausdorff s GP.unitInterval).toReal :=
      (ENNReal.ofReal_le_iff_le_toReal htop).mp (hbound δ hδ)
    linarith
  have hdim_upper : dimH GP.unitInterval ≤ 1 := by
    by_contra h
    obtain ⟨a, ha, had⟩ :=
      ENNReal.lt_iff_exists_nnreal_btwn.mp (lt_of_not_ge h)
    have ha' : (1 : ℝ) < (a : ℝ) := by exact_mod_cast ha
    have hb : dimH GP.unitInterval ≤ (a : ℝ≥0∞) :=
      dimH_le_of_hausdorffMeasure_ne_top (d := a) (by
        rw [upper_native (a : ℝ) ha']
        exact ENNReal.zero_ne_top)
    exact (not_lt_of_ge hb) had
  have hdim_lower : (1 : ℝ≥0∞) ≤ dimH GP.unitInterval := by
    apply ENNReal.le_of_forall_pos_nnreal_lt
    intro s hs hs1
    have hs' : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
    have hs1' : (s : ℝ) < 1 := by exact_mod_cast hs1
    apply le_dimH_of_hausdorffMeasure_eq_top (d := s)
    rw [← h_T001.2 GP.unitInterval (s : ℝ) hs']
    exact lower (s : ℝ) hs' hs1'
  exact ⟨le_antisymm hdim_upper hdim_lower, upper, lower⟩

theorem T004 (n : ℕ) (E : Set (GP.Space n)) (h_T001 : (∀ (m : ℕ) (A : Set (GP.Space m)), 0 ≤ dimH A ∧
  ∀ (s : ℝ), 0 < s →
    GP.hausdorff s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (dimH A < ENNReal.ofReal s → GP.hausdorff s A = 0) ∧
    (ENNReal.ofReal s < dimH A → GP.hausdorff s A = ⊤) ∧
    (GP.hausdorff s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GP.hausdorff s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) ∧ (∀ (A : Set ℝ) (s : ℝ), 0 < s →
    GP.hausdorff s A = MeasureTheory.Measure.hausdorffMeasure s A)) (h_T002 : dimH E < ⊤ ∧ 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧
  (n = 0 → E = Set.univ ∧ (∃ x : GP.Space n, E = {x}) ∧ dimH E = 0) ∧
  ∀ (s δ : ℝ), 0 < s → 0 < δ → GP.content s δ E < ⊤) (h_T003 : dimH GP.unitInterval = 1 ∧
  (∀ a : ℝ, 1 < a → GP.hausdorff a GP.unitInterval = 0) ∧
  (∀ s : ℝ, 0 < s → s < 1 → GP.hausdorff s GP.unitInterval = ⊤)) :
    n = 0 → dimH (GP.cylinder E) ≤ dimH E + 1 := by
  intro hn
  subst n
  rcases h_T002.2.2.2.1 rfl with ⟨hE, _, hD⟩
  let f : ℝ → GP.Space (0 + 1) := fun t => GP.join (0 : GP.Space 0) t
  have hf : Isometry f := by
    apply Isometry.of_dist_eq
    intro t u
    have hs : dist (f t) (f u) ^ 2 = dist t u ^ 2 := by
      rw [EuclideanSpace.dist_sq_eq]
      simp [f, GP.join, Fin.snoc_zero]
    nlinarith [dist_nonneg (x := f t) (y := f u), dist_nonneg (x := t) (y := u)]
  have himage : f '' GP.unitInterval = GP.cylinder E := by
    ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      constructor
      · rw [hE]
        trivial
      · simpa [f, GP.vertical, GP.join, Fin.snoc_zero] using ht
    · intro hz
      refine ⟨GP.vertical z, hz.2, ?_⟩
      apply PiLp.ext
      intro i
      fin_cases i
      rfl
  have hbound : ∀ a : ℝ, 1 < a → dimH (GP.cylinder E) ≤ ENNReal.ofReal a := by
    intro a ha
    have ha0 : 0 < a := lt_trans zero_lt_one ha
    have hmeasure :
        MeasureTheory.Measure.hausdorffMeasure a (GP.cylinder E) =
          MeasureTheory.Measure.hausdorffMeasure a GP.unitInterval := by
      rw [← himage]
      exact hf.hausdorffMeasure_image (Or.inl ha0.le) GP.unitInterval
    have hz : GP.hausdorff a (GP.cylinder E) = 0 := calc
      GP.hausdorff a (GP.cylinder E) =
          MeasureTheory.Measure.hausdorffMeasure a (GP.cylinder E) :=
        ((h_T001.1 1 (GP.cylinder E)).2 a ha0).1
      _ = MeasureTheory.Measure.hausdorffMeasure a GP.unitInterval := hmeasure
      _ = GP.hausdorff a GP.unitInterval := (h_T001.2 GP.unitInterval a ha0).symm
      _ = 0 := h_T003.2.1 a ha
    exact ((h_T001.1 1 (GP.cylinder E)).2 a ha0).2.2.2.1 hz
  rw [hD, zero_add (1 : ℝ≥0∞)]
  have hd : dimH (GP.cylinder E) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hbound 2 (by norm_num))
  apply (ENNReal.toReal_le_toReal hd (by simp)).mp
  simp only [ENNReal.toReal_one]
  apply le_of_forall_gt_imp_ge_of_dense
  intro a ha
  exact ENNReal.toReal_le_of_le_ofReal (le_trans zero_le_one ha.le) (hbound a ha)

theorem T005 (n : ℕ) (E : Set (GP.Space n)) (h_T001 : (∀ (m : ℕ) (A : Set (GP.Space m)), 0 ≤ dimH A ∧
  ∀ (s : ℝ), 0 < s →
    GP.hausdorff s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (dimH A < ENNReal.ofReal s → GP.hausdorff s A = 0) ∧
    (ENNReal.ofReal s < dimH A → GP.hausdorff s A = ⊤) ∧
    (GP.hausdorff s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GP.hausdorff s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) ∧ (∀ (A : Set ℝ) (s : ℝ), 0 < s →
    GP.hausdorff s A = MeasureTheory.Measure.hausdorffMeasure s A)) (h_T002 : dimH E < ⊤ ∧ 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧
  (n = 0 → E = Set.univ ∧ (∃ x : GP.Space n, E = {x}) ∧ dimH E = 0) ∧
  ∀ (s δ : ℝ), 0 < s → 0 < δ → GP.content s δ E < ⊤) :
    1 ≤ n → ∀ (q : ℝ), dimH E < ENNReal.ofReal q →
  ∀ (δ ε : ℝ), 0 < δ → 0 < ε →
    GP.content (q + 1) δ (GP.cylinder E) ≤
      ENNReal.ofReal (2 * (Real.sqrt 2) ^ (q + 1) * ε) := by
  classical
  have initial : ∀ (q δ ε : ℝ), dimH E < ENNReal.ofReal q → 0 < δ → 0 < ε →
    ∃ (r : ℝ) (W : ℕ → Set (GP.Space n)),
      0 < q ∧ 0 < r ∧ r ≤ 1 ∧ Real.sqrt 2 * r ≤ δ ∧
        GP.Cover E r W ∧ GP.cost q W < ENNReal.ofReal (ε/2) := by
    intro q δ ε hdim hδ hε
    have hq : 0 < q := ENNReal.ofReal_pos.mp (lt_of_le_of_lt bot_le hdim)
    have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    let r : ℝ := min 1 (δ / Real.sqrt 2)
    have hr : 0 < r := lt_min zero_lt_one (div_pos hδ hs)
    have hr1 : r ≤ 1 := min_le_left _ _
    have hrδ : Real.sqrt 2 * r ≤ δ := by
      have h := (le_div_iff₀ hs).mp (min_le_right 1 (δ / Real.sqrt 2))
      simpa only [mul_comm] using h
    have hH : GP.hausdorff q E = 0 := (h_T001.1 n E).2 q hq |>.2.1 hdim
    have hzero : GP.content q r E = 0 := by
      apply le_antisymm _ bot_le
      calc GP.content q r E ≤ GP.hausdorff q E :=
             le_iSup_of_le r (le_iSup_of_le hr le_rfl)
           _ = 0 := hH
    have hex : GP.content q r E < ENNReal.ofReal (ε/2) := by
      rw [hzero]
      exact ENNReal.ofReal_pos.mpr (half_pos hε)
    simp only [GP.content, iInf_lt_iff, exists_prop] at hex
    obtain ⟨W, hW, hc⟩ := hex
    exact ⟨r, W, hq, hr, hr1, hrδ, hW, hc⟩
  have regular : 1 ≤ n → ∀ (q r ε : ℝ) (W : ℕ → Set (GP.Space n)),
    0 < q → 0 < r → 0 < ε → GP.Cover E r W →
    GP.cost q W < ENNReal.ofReal (ε/2) →
    ∃ (U : {i : ℕ // (W i).Nonempty} → Set (GP.Space n))
      (d : {i : ℕ // (W i).Nonempty} → ℝ),
      (E ⊆ ⋃ i, U i) ∧
      (∀ i, 0 < d i ∧ d i ≤ r ∧ Metric.ediam (U i) = ENNReal.ofReal (d i)) ∧
      (∑' i, ENNReal.ofReal ((d i)^q)) < ENNReal.ofReal ε := by
    classical
    have betas : ∀ (q r ε : ℝ), 0 < q → 0 < r → 0 < ε →
      ∃ b : ℕ → ℝ, (∀ i, 0 < b i ∧ b i ≤ r ∧ (b i) ^ q ≤ ε / 8 * ((1:ℝ)/2)^i) ∧
        (∑' i, ENNReal.ofReal (ε / 8 * ((1:ℝ)/2)^i)) = ENNReal.ofReal (ε / 4) := by
      intro q r ε hq hr hε
      let a : ℕ → ℝ := fun i => ε / 8 * ((1:ℝ)/2)^i
      let b : ℕ → ℝ := fun i => min (r/2) ((a i) ^ q⁻¹)
      have ha : ∀ i, 0 < a i := fun i => by dsimp [a]; positivity
      refine ⟨b, ?_, ?_⟩
      · intro i
        have hb : 0 < b i := lt_min (half_pos hr) (Real.rpow_pos_of_pos (ha i) _)
        refine ⟨hb, (min_le_left _ _).trans (by linarith), ?_⟩
        calc (b i) ^ q ≤ ((a i) ^ q⁻¹) ^ q :=
              Real.rpow_le_rpow hb.le (min_le_right _ _) hq.le
             _ = a i := Real.rpow_inv_rpow (ha i).le hq.ne'
      · rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => (ha i).le)
          (summable_geometric_two.mul_left (ε/8)), tsum_mul_left, tsum_geometric_two]
        congr 1
        ring
    intro hn q r ε W hq hr hε hW hcost
    letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    haveI : Nontrivial (GP.Space n) := inferInstance
    obtain ⟨b, hb, hsum⟩ := betas q r ε hq hr hε
    let K := {i : ℕ // (W i).Nonempty}
    let x : K → GP.Space n := fun i => i.property.choose
    let U : K → Set (GP.Space n) := fun i =>
      if Metric.ediam (W i) = 0 then Metric.ball (x i) (b i / 2) else W i
    let d : K → ℝ := fun i =>
      if Metric.ediam (W i) = 0 then b i else Metric.diam (W i)
    have hd : ∀ i, 0 < d i ∧ d i ≤ r ∧ Metric.ediam (U i) = ENNReal.ofReal (d i) := by
      intro i
      have ht : Metric.ediam (W i) ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hW.2 i)
      dsimp [U, d]
      split_ifs with hi
      · refine ⟨(hb i).1, (hb i).2.1, ?_⟩
        have heq : Metric.diam (Metric.ball (x i) (b i / 2)) = b i := by
          rw [Metric.diam_ball_eq _ (by linarith [(hb i).1])]
          ring
        exact (ENNReal.ofReal_toReal (Metric.isBounded_ball (x := x i) (r := b i / 2)).ediam_ne_top).symm.trans
          (congrArg ENNReal.ofReal heq)
      · exact ⟨ENNReal.toReal_pos hi ht,
          ENNReal.toReal_le_of_le_ofReal hr.le (hW.2 i), (ENNReal.ofReal_toReal ht).symm⟩
    have hsub : ∀ i : K, W i ⊆ U i := by
      intro i y hy
      dsimp [U]
      split_ifs with hi
      · have hxy : y = x i := (Metric.ediam_eq_zero_iff.mp hi) hy i.property.choose_spec
        rw [hxy]
        exact Metric.mem_ball_self (half_pos (hb i).1)
      · exact hy
    refine ⟨U, d, ?_, hd, ?_⟩
    · intro y hy
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hW.1 hy)
      exact Set.mem_iUnion.mpr ⟨⟨i, y, hi⟩, hsub ⟨i, y, hi⟩ hi⟩
    · have hpoint : ∀ i : K, ENNReal.ofReal ((d i)^q) ≤
          (⨆ (_ : (W i).Nonempty), Metric.ediam (W i)^q) +
            ENNReal.ofReal (ε/8 * ((1:ℝ)/2)^(i:ℕ)) := by
        intro i
        dsimp [d]
        split_ifs with hi
        · exact (ENNReal.ofReal_le_ofReal (hb i).2.2).trans (le_add_left le_rfl)
        · have heq : ENNReal.ofReal (Metric.diam (W i)^q) = Metric.ediam (W i)^q := by
            rw [← ENNReal.ofReal_rpow_of_nonneg Metric.diam_nonneg hq.le]
            congr 1
            exact ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hW.2 i))
          rw [heq]
          exact le_add_of_le_left (le_iSup_of_le i.property le_rfl)
      calc
        (∑' i, ENNReal.ofReal ((d i)^q)) ≤
            ∑' i : K, ((⨆ (_ : (W i).Nonempty), Metric.ediam (W i)^q) +
              ENNReal.ofReal (ε/8 * ((1:ℝ)/2)^(i:ℕ))) := ENNReal.tsum_le_tsum hpoint
        _ ≤ GP.cost q W + ENNReal.ofReal (ε/4) := by
          rw [ENNReal.tsum_add]
          exact add_le_add
            (ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective
              (fun i => ⨆ (_ : (W i).Nonempty), Metric.ediam (W i)^q))
            ((ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective
              (fun i => ENNReal.ofReal (ε/8 * ((1:ℝ)/2)^i))).trans_eq hsum)
        _ ≤ ENNReal.ofReal (ε/2) + ENNReal.ofReal (ε/4) := add_le_add hcost.le le_rfl
        _ = ENNReal.ofReal (ε/2+ε/4) := (ENNReal.ofReal_add (by positivity) (by positivity)).symm
        _ < ENNReal.ofReal ε := (ENNReal.ofReal_lt_ofReal_iff hε).mpr (by linarith)
  have productCover : ∀ {ι : Type} [Encodable ι] (q δ ε r : ℝ)
      (U : ι → Set (GP.Space n)) (d : ι → ℝ),
      0 < q → r ≤ 1 → Real.sqrt 2 * r ≤ δ →
      E ⊆ ⋃ i, U i →
      (∀ i, 0 < d i ∧ d i ≤ r ∧ Metric.ediam (U i) = ENNReal.ofReal (d i)) →
      (∑' i, ENNReal.ofReal ((d i)^q)) ≤ ENNReal.ofReal ε →
      GP.content (q+1) δ (GP.cylinder E) ≤
        ENNReal.ofReal (2 * (Real.sqrt 2) ^ (q+1) * ε) := by
    classical
    have mesh : ∀ (r : ℝ), 0 < r → r ≤ 1 →
      ∃ (N : ℕ) (J : Fin N → Set ℝ), 0 < N ∧
        (↑N : ℝ) ≤ 2 / r ∧
        GP.unitInterval ⊆ ⋃ j, J j ∧
        (∀ j, Metric.ediam (J j) ≤ ENNReal.ofReal r) := by
      intro r hr hr1
      let N : ℕ := ⌈1 / r⌉₊
      have hN : 0 < N := Nat.ceil_pos.mpr (one_div_pos.mpr hr)
      have hNr : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
      have hceil : 1 / r ≤ (N : ℝ) := Nat.le_ceil _
      have hsize : (N : ℝ) ≤ 2 / r := by
        have h := (Nat.ceil_lt_add_one (le_of_lt (one_div_pos.mpr hr))).le
        have h1 : 1 ≤ 1 / r := (le_div_iff₀ hr).mpr (by simpa using hr1)
        dsimp [N]
        calc _ ≤ 1 / r + 1 := h
             _ ≤ 1 / r + 1 / r := add_le_add_right h1 _
             _ = 2 / r := by ring
      have hinv : 1 / (N : ℝ) ≤ r := by
        apply (div_le_iff₀ hNr).mpr
        have h := (div_le_iff₀ hr).mp hceil
        nlinarith
      let J : Fin N → Set ℝ := fun j => Set.Icc ((j : ℝ) / N) (((j : ℝ) + 1) / N)
      refine ⟨N, J, hN, hsize, ?_, ?_⟩
      · have cov : ∀ k : ℕ, k ≤ N → ∀ t : ℝ, 0 ≤ t → t ≤ (k : ℝ) / N →
            ∃ j : Fin N, t ∈ J j := by
          intro k
          induction k with
          | zero =>
            intro _ t ht ht'
            have ht0 : t ≤ 0 := by simpa using ht'
            have ht0 : t = 0 := le_antisymm ht0 ht
            subst t
            refine ⟨⟨0, hN⟩, ?_⟩
            simp [J, le_of_lt (one_div_pos.mpr hNr)]
          | succ k ih =>
            intro hk t ht ht'
            by_cases htk : t ≤ (k : ℝ) / N
            · exact ih (by omega) t ht htk
            · refine ⟨⟨k, by omega⟩, ?_, ?_⟩
              · exact (lt_of_not_ge htk).le
              · simpa [Nat.cast_add, Nat.cast_one] using ht'
        intro t ht
        obtain ⟨j, hj⟩ := cov N le_rfl t ht.1 (by simpa [ne_of_gt hNr] using ht.2)
        exact Set.mem_iUnion.mpr ⟨j, hj⟩
      · intro j
        dsimp [J]
        rw [Real.ediam_Icc]
        apply ENNReal.ofReal_le_ofReal
        calc ((j : ℝ) + 1) / N - (j : ℝ) / N = 1 / N := by ring
             _ ≤ r := hinv
    have productDiam : ∀ (U : Set (GP.Space n)) (J : Set ℝ) (r : ℝ), 0 ≤ r →
      Metric.ediam U ≤ ENNReal.ofReal r → Metric.ediam J ≤ ENNReal.ofReal r →
      Metric.ediam {z : GP.Space (n+1) | GP.horizontal z ∈ U ∧ GP.vertical z ∈ J}
        ≤ ENNReal.ofReal (Real.sqrt 2 * r) := by
      intro U J r hr hU hJ
      apply Metric.ediam_le
      intro z hz w hw
      rw [edist_dist]
      apply ENNReal.ofReal_le_ofReal
      have hdU : dist (GP.horizontal z) (GP.horizontal w) ≤ r := by
        have h := Metric.edist_le_of_ediam_le hz.1 hw.1 hU
        rwa [edist_dist, ENNReal.ofReal_le_ofReal_iff hr] at h
      have hdJ : dist (GP.vertical z) (GP.vertical w) ≤ r := by
        have h := Metric.edist_le_of_ediam_le hz.2 hw.2 hJ
        rwa [edist_dist, ENNReal.ofReal_le_ofReal_iff hr] at h
      have hsq : dist z w ^ 2 =
          dist (GP.horizontal z) (GP.horizontal w) ^ 2 +
            dist (GP.vertical z) (GP.vertical w) ^ 2 := by
        simp only [EuclideanSpace.dist_sq_eq, Fin.sum_univ_castSucc,
          GP.horizontal, GP.vertical, PiLp.toLp_apply]
      have hsqrt : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have hnon : 0 ≤ Real.sqrt 2 * r := mul_nonneg (Real.sqrt_nonneg _) hr
      have hU2 : dist (GP.horizontal z) (GP.horizontal w) ^ 2 ≤ r ^ 2 := by
        nlinarith [dist_nonneg (x := GP.horizontal z) (y := GP.horizontal w)]
      have hJ2 : dist (GP.vertical z) (GP.vertical w) ^ 2 ≤ r ^ 2 := by
        nlinarith [dist_nonneg (x := GP.vertical z) (y := GP.vertical w)]
      have h2 : dist z w ^ 2 ≤ (Real.sqrt 2 * r) ^ 2 := by
        rw [mul_pow, hsqrt]
        linarith
      nlinarith [dist_nonneg (x := z) (y := w)]
    have compress : ∀ {X : Type} [MetricSpace X] {ι : Type} [Encodable ι]
        (s δ : ℝ) (A : Set X) (V : ι → Set X),
        A ⊆ ⋃ i, V i → (∀ i, Metric.ediam (V i) ≤ ENNReal.ofReal δ) →
        GP.content s δ A ≤ ∑' i, (Metric.ediam (V i)) ^ s := by
      intro X _ ι _ s δ A V hcov hdiam
      classical
      let U : ℕ → Set X := fun j => ⋃ b ∈ Encodable.decode₂ ι j, V b
      have hU : GP.Cover A δ U := by
        constructor
        · simpa only [U, Encodable.iUnion_decode₂] using hcov
        · intro j
          dsimp [U]
          rw [Metric.ediam_iUnion_mem_option]
          exact iSup_le fun b => iSup_le fun _ => hdiam b
      calc
        GP.content s δ A ≤ GP.cost s U := iInf_le_of_le U (iInf_le _ hU)
        _ = ∑' i, ⨆ (_ : (V i).Nonempty), Metric.ediam (V i) ^ s := by
          exact tsum_iUnion_decode₂ (fun t : Set X => ⨆ (_ : t.Nonempty), Metric.ediam t ^ s)
            (by simp) V
        _ ≤ ∑' i, Metric.ediam (V i) ^ s := ENNReal.tsum_le_tsum (fun i => iSup_le fun _ => le_rfl)
    have numerical : ∀ (q r : ℝ) (N : ℕ), 0 < r → (N : ℝ) ≤ 2 / r →
      (N : ℝ≥0∞) * ENNReal.ofReal (Real.sqrt 2 * r) ^ (q+1) ≤
        ENNReal.ofReal (2 * (Real.sqrt 2) ^ (q+1)) * ENNReal.ofReal (r^q) := by
      intro q r N hr hN
      have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
      have hNr : (N : ℝ) * r ≤ 2 := (le_div_iff₀ hr).mp hN
      have heq : (Real.sqrt 2 * r) ^ (q+1) = (Real.sqrt 2) ^ (q+1) * r^q * r := by
        rw [Real.mul_rpow hs.le hr.le, Real.rpow_add hr, Real.rpow_one]
        ring
      have hreal : (N : ℝ) * (Real.sqrt 2 * r) ^ (q+1) ≤
          (2 * (Real.sqrt 2) ^ (q+1)) * r^q := by
        rw [heq]
        calc (N : ℝ) * ((Real.sqrt 2)^(q+1) * r^q * r) =
            ((N : ℝ)*r) * ((Real.sqrt 2)^(q+1) * r^q) := by ring
             _ ≤ 2 * ((Real.sqrt 2)^(q+1) * r^q) :=
               mul_le_mul_of_nonneg_right hNr (by positivity)
             _ = _ := by ring
      have hcast : (N : ℝ≥0∞) = ENNReal.ofReal (N : ℝ) := by simp
      rw [hcast, ENNReal.ofReal_rpow_of_pos (mul_pos hs hr),
        ← ENNReal.ofReal_mul (Nat.cast_nonneg N),
        ← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal hreal
    intro ι _ q δ ε r U d hq hr1 hrδ hcov hd hsum
    choose N J hN hsize hJcov hJdiam using
      fun i => mesh (d i) (hd i).1 ((hd i).2.1.trans hr1)
    let V : (Σ i, Fin (N i)) → Set (GP.Space (n+1)) := fun p =>
      {z | GP.horizontal z ∈ U p.1 ∧ GP.vertical z ∈ J p.1 p.2}
    have hVdiam : ∀ p, Metric.ediam (V p) ≤ ENNReal.ofReal (Real.sqrt 2 * d p.1) := by
      intro p
      exact productDiam (U p.1) (J p.1 p.2) (d p.1) (hd p.1).1.le
        (hd p.1).2.2.le (hJdiam p.1 p.2)
    have hVcov : GP.cylinder E ⊆ ⋃ p, V p := by
      intro z hz
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov hz.1)
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hJcov i hz.2)
      exact Set.mem_iUnion.mpr ⟨⟨i,j⟩, hi, hj⟩
    calc
      GP.content (q+1) δ (GP.cylinder E) ≤
          ∑' p, Metric.ediam (V p) ^ (q+1) :=
        compress (q+1) δ (GP.cylinder E) V hVcov (fun p =>
          (hVdiam p).trans (ENNReal.ofReal_le_ofReal
            ((mul_le_mul_of_nonneg_left (hd p.1).2.1 (Real.sqrt_nonneg _)).trans hrδ)))
      _ ≤ ∑' p : Σ i, Fin (N i), ENNReal.ofReal (Real.sqrt 2 * d p.1) ^ (q+1) :=
        ENNReal.tsum_le_tsum (fun p => ENNReal.rpow_le_rpow (hVdiam p) (by linarith))
      _ = ∑' i, (N i : ℝ≥0∞) * ENNReal.ofReal (Real.sqrt 2 * d i) ^ (q+1) := by
        rw [ENNReal.tsum_sigma' (fun p : Σ i, Fin (N i) =>
          ENNReal.ofReal (Real.sqrt 2 * d p.1) ^ (q+1))]
        simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ ∑' i, ENNReal.ofReal (2 * (Real.sqrt 2)^(q+1)) * ENNReal.ofReal ((d i)^q) :=
        ENNReal.tsum_le_tsum (fun i => numerical q (d i) (N i) (hd i).1 (hsize i))
      _ = ENNReal.ofReal (2 * (Real.sqrt 2)^(q+1)) * ∑' i, ENNReal.ofReal ((d i)^q) :=
        ENNReal.tsum_mul_left
      _ ≤ ENNReal.ofReal (2 * (Real.sqrt 2)^(q+1)) * ENNReal.ofReal ε :=
        mul_le_mul_left' hsum _
      _ = ENNReal.ofReal (2 * (Real.sqrt 2)^(q+1) * ε) :=
        (ENNReal.ofReal_mul (by positivity)).symm
  intro hn q hdim δ ε hδ hε
  obtain ⟨r, W, hq, hr, hr1, hrδ, hW, hc⟩ := initial q δ ε hdim hδ hε
  obtain ⟨U, d, hcov, hd, hsum⟩ := regular hn q r ε W hq hr hε hW hc
  exact productCover q δ ε r U d hq hr1 hrδ hcov hd hsum.le

theorem T006 (n : ℕ) (E : Set (GP.Space n)) (h_T001 : (∀ (m : ℕ) (A : Set (GP.Space m)), 0 ≤ dimH A ∧
  ∀ (s : ℝ), 0 < s →
    GP.hausdorff s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (dimH A < ENNReal.ofReal s → GP.hausdorff s A = 0) ∧
    (ENNReal.ofReal s < dimH A → GP.hausdorff s A = ⊤) ∧
    (GP.hausdorff s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GP.hausdorff s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) ∧ (∀ (A : Set ℝ) (s : ℝ), 0 < s →
    GP.hausdorff s A = MeasureTheory.Measure.hausdorffMeasure s A)) (h_T002 : dimH E < ⊤ ∧ 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧
  (n = 0 → E = Set.univ ∧ (∃ x : GP.Space n, E = {x}) ∧ dimH E = 0) ∧
  ∀ (s δ : ℝ), 0 < s → 0 < δ → GP.content s δ E < ⊤) (h_T004 : n = 0 → dimH (GP.cylinder E) ≤ dimH E + 1) (h_T005 : 1 ≤ n → ∀ (q : ℝ), dimH E < ENNReal.ofReal q →
  ∀ (δ ε : ℝ), 0 < δ → 0 < ε →
    GP.content (q + 1) δ (GP.cylinder E) ≤
      ENNReal.ofReal (2 * (Real.sqrt 2) ^ (q + 1) * ε)) :
    dimH (GP.cylinder E) ≤ dimH E + 1 ∧ dimH (GP.cylinder E) < ⊤ := by
  have hbound : dimH (GP.cylinder E) ≤ dimH E + 1 := by
    by_cases hn : n = 0
    · exact h_T004 hn
    · have hn' : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      have hqbound : ∀ q : ℝ, dimH E < ENNReal.ofReal q →
          dimH (GP.cylinder E) ≤ ENNReal.ofReal (q + 1) := by
        intro q hq
        have hqreal : (dimH E).toReal < q :=
          (ENNReal.lt_ofReal_iff_toReal_lt h_T002.1.ne).1 hq
        have hqpos : 0 < q := lt_of_le_of_lt ENNReal.toReal_nonneg hqreal
        have hC : 0 < 2 * (Real.sqrt 2) ^ (q + 1) := by positivity
        have hcontent : ∀ δ : ℝ, 0 < δ →
            GP.content (q + 1) δ (GP.cylinder E) = 0 := by
          intro δ hδ
          apply le_antisymm _ zero_le
          apply ENNReal.le_of_forall_pos_le_add
          intro ε hε _
          have hεr : 0 < (ε : ℝ) := by exact_mod_cast hε
          have hεdiv : 0 < (ε : ℝ) / (2 * (Real.sqrt 2) ^ (q + 1)) :=
            div_pos hεr hC
          have hconv : ENNReal.ofReal
              (2 * (Real.sqrt 2) ^ (q + 1) *
                ((ε : ℝ) / (2 * (Real.sqrt 2) ^ (q + 1)))) = (ε : ℝ≥0∞) := by
            rw [mul_div_cancel₀ (ε : ℝ) (ne_of_gt hC), ENNReal.ofReal_coe_nnreal]
          simpa only [zero_add, hconv] using
            h_T005 hn' q hq δ ((ε : ℝ) / (2 * (Real.sqrt 2) ^ (q + 1))) hδ hεdiv
        have hhaus : GP.hausdorff (q + 1) (GP.cylinder E) = 0 := by
          apply le_antisymm _ zero_le
          change (⨆ (δ : ℝ) (_ : 0 < δ), GP.content (q + 1) δ (GP.cylinder E)) ≤ 0
          exact iSup_le fun δ => iSup_le fun hδ => (hcontent δ hδ).le
        exact (h_T001.1 (n + 1) (GP.cylinder E)).2 (q + 1) (by linarith) |>.2.2.2.1 hhaus
      have hfixed : dimH E < ENNReal.ofReal ((dimH E).toReal + 1) := by
        apply (ENNReal.lt_ofReal_iff_toReal_lt h_T002.1.ne).2
        linarith
      have hfinite : dimH (GP.cylinder E) < ⊤ :=
        lt_of_le_of_lt (hqbound _ hfixed) ENNReal.ofReal_lt_top
      apply ENNReal.le_of_forall_pos_le_add
      intro ε hε _
      have hεr : 0 < (ε : ℝ) := by exact_mod_cast hε
      have hq : dimH E < ENNReal.ofReal ((dimH E).toReal + (ε : ℝ)) := by
        apply (ENNReal.lt_ofReal_iff_toReal_lt h_T002.1.ne).2
        linarith
      have hconv : ENNReal.ofReal ((dimH E).toReal + (ε : ℝ) + 1) =
          dimH E + 1 + (ε : ℝ≥0∞) := by
        rw [ENNReal.ofReal_add (add_nonneg ENNReal.toReal_nonneg ε.coe_nonneg) (by norm_num),
          ENNReal.ofReal_add ENNReal.toReal_nonneg ε.coe_nonneg,
          ENNReal.ofReal_toReal h_T002.1.ne, ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_one]
        ac_rfl
      simpa only [hconv] using hqbound _ hq
  exact ⟨hbound, lt_of_le_of_lt hbound (ENNReal.add_lt_top.mpr ⟨h_T002.1, by simp⟩)⟩

theorem T007 (n : ℕ) (E : Set (GP.Space n)) (h_T002 : dimH E < ⊤ ∧ 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧
  (n = 0 → E = Set.univ ∧ (∃ x : GP.Space n, E = {x}) ∧ dimH E = 0) ∧
  ∀ (s δ : ℝ), 0 < s → 0 < δ → GP.content s δ E < ⊤) :
    ∀ (s δ : ℝ), 0 < s → 0 < δ →
  ∀ (V : ℕ → Set (GP.Space (n + 1))), GP.Cover (GP.cylinder E) δ V →
  ∀ ε : ℝ, 0 < ε → ∃ J : ℕ → Set ℝ,
    (∀ i, IsOpen (J i)) ∧
    (∀ i, GP.vertical '' (V i) ⊆ J i) ∧
    (∀ i, MeasureTheory.volume (J i) ≤ Metric.ediam (V i) +
      ENNReal.ofReal (ε * (1 / 2 : ℝ) ^ (i + 1) /
        (1 + (Metric.diam (V i)) ^ s))) ∧
    (∀ t ∈ GP.unitInterval,
      GP.content s δ E ≤
        ∑' i, (J i).indicator (fun _ => (Metric.ediam (V i)) ^ s) t) := by
  classical
  have hproj : LipschitzWith 1 (@GP.horizontal n) ∧ LipschitzWith 1 (@GP.vertical n) := by
    have hsplit (x y : GP.Space (n+1)) : dist x y ^ 2 =
        dist (GP.horizontal x) (GP.horizontal y) ^ 2 +
          dist (GP.vertical x) (GP.vertical y) ^ 2 := by
      simp only [EuclideanSpace.dist_sq_eq, Fin.sum_univ_castSucc, GP.horizontal, GP.vertical]
    constructor
    · apply LipschitzWith.of_dist_le_mul
      intro x y
      simp only [NNReal.coe_one, one_mul]
      nlinarith [hsplit x y, sq_nonneg (dist (GP.vertical x) (GP.vertical y)),
        dist_nonneg (x := GP.horizontal x) (y := GP.horizontal y),
        dist_nonneg (x := x) (y := y)]
    · apply LipschitzWith.of_dist_le_mul
      intro x y
      simp only [NNReal.coe_one, one_mul]
      nlinarith [hsplit x y, sq_nonneg (dist (GP.horizontal x) (GP.horizontal y)),
        dist_nonneg (x := GP.vertical x) (y := GP.vertical y),
        dist_nonneg (x := x) (y := y)]
  rcases hproj with ⟨hh, hv⟩
  have hinterval : ∀ (V : Set (GP.Space (n+1))), Bornology.IsBounded V →
      ∀ η : ℝ, 0 < η → ∃ J : Set ℝ, IsOpen J ∧ GP.vertical '' V ⊆ J ∧
        MeasureTheory.volume J ≤ Metric.ediam V + ENNReal.ofReal η := by
    classical
    intro V hV η hη
    let B : Set ℝ := GP.vertical '' V
    have hB : Bornology.IsBounded B := hv.isBounded_image hV
    have hd : Metric.diam B ≤ Metric.diam V := by
      simpa only [NNReal.coe_one, one_mul] using hv.diam_image_le V hV
    have hconv : ENNReal.ofReal (Metric.diam V) = Metric.ediam V :=
      ENNReal.ofReal_toReal hV.ediam_ne_top
    by_cases hne : V.Nonempty
    · refine ⟨Set.Ioo (sInf B - η / 2) (sSup B + η / 2), isOpen_Ioo, ?_, ?_⟩
      · intro t ht
        have ht' := hB.subset_Icc_sInf_sSup ht
        constructor <;> linarith [ht'.1, ht'.2]
      · rw [Real.volume_Ioo]
        have hh : sSup B + η / 2 - (sInf B - η / 2) = Metric.diam B + η := by
          rw [Real.diam_eq hB]
          ring
        rw [hh]
        calc
          ENNReal.ofReal (Metric.diam B + η) ≤ ENNReal.ofReal (Metric.diam V + η) :=
            ENNReal.ofReal_le_ofReal (by linarith)
          _ = Metric.ediam V + ENNReal.ofReal η := by
            rw [ENNReal.ofReal_add Metric.diam_nonneg hη.le, hconv]
    · have hem : V = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      refine ⟨∅, isOpen_empty, ?_, ?_⟩ <;> simp [hem]
  intro s δ hs hδ V hV ε hε
  have hcfinite : GP.content s δ E < ⊤ := h_T002.2.2.2.2 s δ hs hδ
  have hb (i : ℕ) : Bornology.IsBounded (V i) :=
    Metric.isBounded_iff_ediam_ne_top.mpr
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hV.2 i))
  let η : ℕ → ℝ := fun i => ε * (1 / 2 : ℝ) ^ (i + 1) /
      (1 + (Metric.diam (V i)) ^ s)
  have hη (i : ℕ) : 0 < η i := by
    dsimp [η]
    have hp : 0 ≤ (Metric.diam (V i)) ^ s := Real.rpow_nonneg Metric.diam_nonneg s
    positivity
  choose J hopen hsub hvol using fun i => hinterval (V i) (hb i) (η i) (hη i)
  refine ⟨J, hopen, hsub, hvol, ?_⟩
  intro t ht
  let W : ℕ → Set (GP.Space n) := fun i =>
    if t ∈ J i then GP.horizontal '' (V i) else ∅
  have hd (i : ℕ) : Metric.ediam (GP.horizontal '' V i) ≤ Metric.ediam (V i) := by
    simpa only [ENNReal.coe_one, one_mul] using hh.ediam_image_le (V i)
  have hW : GP.Cover E δ W := by
    constructor
    · intro x hx
      have hz : GP.join x t ∈ GP.cylinder E := by
        change GP.horizontal (GP.join x t) ∈ E ∧ GP.vertical (GP.join x t) ∈ GP.unitInterval
        simpa [GP.horizontal, GP.vertical, GP.join] using And.intro hx ht
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hV.1 hz)
      have hti : t ∈ J i := by
        apply hsub i
        exact ⟨GP.join x t, hi, by simp [GP.vertical, GP.join]⟩
      apply Set.mem_iUnion.mpr
      refine ⟨i, ?_⟩
      simp only [W, if_pos hti]
      exact ⟨GP.join x t, hi, by simp [GP.horizontal, GP.join]⟩
    · intro i
      dsimp [W]
      split_ifs
      · exact (hd i).trans (hV.2 i)
      · simp
  have hc : GP.content s δ E ≤ GP.cost s W := by
    exact iInf_le_of_le W (iInf_le_of_le hW le_rfl)
  apply hc.trans
  unfold GP.cost
  apply ENNReal.tsum_le_tsum
  intro i
  by_cases hti : t ∈ J i
  · simp only [Set.indicator_of_mem hti]
    apply iSup_le
    intro hne
    apply ENNReal.rpow_le_rpow _ hs.le
    simpa only [W, if_pos hti] using hd i
  · simp [W, hti, Set.indicator_of_notMem hti]

theorem T008 (n : ℕ) (E : Set (GP.Space n)) (h_T002 : dimH E < ⊤ ∧ 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧
  (n = 0 → E = Set.univ ∧ (∃ x : GP.Space n, E = {x}) ∧ dimH E = 0) ∧
  ∀ (s δ : ℝ), 0 < s → 0 < δ → GP.content s δ E < ⊤) (h_T007 : ∀ (s δ : ℝ), 0 < s → 0 < δ →
  ∀ (V : ℕ → Set (GP.Space (n + 1))), GP.Cover (GP.cylinder E) δ V →
  ∀ ε : ℝ, 0 < ε → ∃ J : ℕ → Set ℝ,
    (∀ i, IsOpen (J i)) ∧
    (∀ i, GP.vertical '' (V i) ⊆ J i) ∧
    (∀ i, MeasureTheory.volume (J i) ≤ Metric.ediam (V i) +
      ENNReal.ofReal (ε * (1 / 2 : ℝ) ^ (i + 1) /
        (1 + (Metric.diam (V i)) ^ s))) ∧
    (∀ t ∈ GP.unitInterval,
      GP.content s δ E ≤
        ∑' i, (J i).indicator (fun _ => (Metric.ediam (V i)) ^ s) t)) :
    ∀ (s δ : ℝ), 0 < s → 0 < δ →
  ∀ (V : ℕ → Set (GP.Space (n + 1))), GP.Cover (GP.cylinder E) δ V →
  ∀ ε : ℝ, 0 < ε →
    GP.content s δ E ≤ GP.cost (s + 1) V + ENNReal.ofReal ε := by
  classical
  intro s δ hs hδ V hV ε hε
  have hcfinite : GP.content s δ E < ⊤ := h_T002.2.2.2.2 s δ hs hδ
  obtain ⟨J, hJopen, hJimage, hJlength, hslice⟩ := h_T007 s δ hs hδ V hV ε hε
  have hfinite (i : ℕ) : Metric.ediam (V i) ≠ ⊤ :=
    (lt_of_le_of_lt (hV.2 i) ENNReal.ofReal_lt_top).ne
  have error_bound (r : ℝ≥0∞) (b : ℝ) (hr : r ≠ ⊤) (hb : 0 ≤ b) :
      ENNReal.ofReal (b / (1 + r.toReal ^ s)) * r ^ s ≤ ENNReal.ofReal b := by
    have hd : 0 ≤ r.toReal := ENNReal.toReal_nonneg
    have hp : 0 ≤ r.toReal ^ s := Real.rpow_nonneg hd s
    have hconv : ENNReal.ofReal (r.toReal ^ s) = r ^ s := by
      rw [← ENNReal.ofReal_rpow_of_nonneg hd hs.le, ENNReal.ofReal_toReal hr]
    rw [← hconv, ← ENNReal.ofReal_mul (div_nonneg hb (by positivity))]
    apply ENNReal.ofReal_le_ofReal
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0 < 1 + r.toReal ^ s)).2
    nlinarith [mul_nonneg hb hp]
  have herr (i : ℕ) :
      ENNReal.ofReal (ε * (1 / 2 : ℝ) ^ (i + 1) /
        (1 + Metric.diam (V i) ^ s)) * Metric.ediam (V i) ^ s ≤
        ENNReal.ofReal (ε * (1 / 2 : ℝ) ^ (i + 1)) := by
    exact error_bound (Metric.ediam (V i)) (ε * (1 / 2 : ℝ) ^ (i + 1))
      (hfinite i) (by positivity)
  have hsumerror :
      (∑' i : ℕ, ENNReal.ofReal (ε * (1 / 2 : ℝ) ^ (i + 1))) =
        ENNReal.ofReal ε := by
    have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = (2 : ℝ≥0∞)⁻¹ := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
      norm_num
    simp_rw [ENNReal.ofReal_mul hε.le,
      ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric_add_one, hhalf,
      ENNReal.one_sub_inv_two, inv_inv,
      ENNReal.inv_mul_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num : (2 : ℝ≥0∞) ≠ ⊤), mul_one]
  have hcost : (∑' i, Metric.ediam (V i) ^ (s + 1)) = GP.cost (s + 1) V := by
    unfold GP.cost
    apply tsum_congr
    intro i
    by_cases hi : (V i).Nonempty
    · simp [hi]
    · have he : V i = ∅ := Set.not_nonempty_iff_eq_empty.mp hi
      simp [he, ENNReal.zero_rpow_of_pos (by linarith : 0 < s + 1)]
  let μ : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict GP.unitInterval
  have hI : MeasurableSet GP.unitInterval := measurableSet_Icc
  have hmass : μ Set.univ = 1 := by
    simp [μ, GP.unitInterval, Real.volume_Icc]
  have hm (i : ℕ) :
      AEMeasurable ((J i).indicator (fun _ : ℝ => Metric.ediam (V i) ^ s)) μ :=
    (measurable_const.indicator (hJopen i).measurableSet).aemeasurable
  calc
    GP.content s δ E = ∫⁻ _ : ℝ, GP.content s δ E ∂μ := by
      rw [MeasureTheory.lintegral_const, hmass, mul_one]
    _ ≤ ∫⁻ t : ℝ, ∑' i, (J i).indicator (fun _ => Metric.ediam (V i) ^ s) t ∂μ := by
      apply MeasureTheory.lintegral_mono_ae
      filter_upwards [MeasureTheory.ae_restrict_mem hI] with t ht
      exact hslice t ht
    _ = ∑' i, ∫⁻ t : ℝ, (J i).indicator (fun _ => Metric.ediam (V i) ^ s) t ∂μ :=
      MeasureTheory.lintegral_tsum hm
    _ ≤ ∑' i, Metric.ediam (V i) ^ s * MeasureTheory.volume (J i) := by
      apply ENNReal.tsum_le_tsum
      intro i
      rw [MeasureTheory.lintegral_indicator_const (hJopen i).measurableSet]
      exact mul_le_mul_left'
        (MeasureTheory.Measure.restrict_le_self
          (s := GP.unitInterval) (μ := MeasureTheory.volume) (J i)) _
    _ ≤ ∑' i, (Metric.ediam (V i) ^ (s + 1) +
        ENNReal.ofReal (ε * (1 / 2 : ℝ) ^ (i + 1))) := by
      apply ENNReal.tsum_le_tsum
      intro i
      have hpow : Metric.ediam (V i) ^ s * Metric.ediam (V i) =
          Metric.ediam (V i) ^ (s + 1) := by
        rw [ENNReal.rpow_add_of_nonneg s 1 hs.le zero_le_one, ENNReal.rpow_one]
      calc
        Metric.ediam (V i) ^ s * MeasureTheory.volume (J i) ≤
            Metric.ediam (V i) ^ s * (Metric.ediam (V i) +
              ENNReal.ofReal (ε * (1 / 2 : ℝ) ^ (i + 1) /
                (1 + Metric.diam (V i) ^ s))) :=
          mul_le_mul_left' (hJlength i) _
        _ = Metric.ediam (V i) ^ (s + 1) +
            Metric.ediam (V i) ^ s *
              ENNReal.ofReal (ε * (1 / 2 : ℝ) ^ (i + 1) /
                (1 + Metric.diam (V i) ^ s)) := by rw [mul_add, hpow]
        _ ≤ Metric.ediam (V i) ^ (s + 1) +
            ENNReal.ofReal (ε * (1 / 2 : ℝ) ^ (i + 1)) := by
          refine add_le_add le_rfl ?_
          rw [mul_comm]
          exact herr i
    _ = GP.cost (s + 1) V + ENNReal.ofReal ε := by
      rw [ENNReal.tsum_add, hcost, hsumerror]

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

theorem T010 (n : ℕ) (E : Set (GP.Space n)) (h_T001 : (∀ (m : ℕ) (A : Set (GP.Space m)), 0 ≤ dimH A ∧
  ∀ (s : ℝ), 0 < s →
    GP.hausdorff s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (dimH A < ENNReal.ofReal s → GP.hausdorff s A = 0) ∧
    (ENNReal.ofReal s < dimH A → GP.hausdorff s A = ⊤) ∧
    (GP.hausdorff s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GP.hausdorff s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) ∧ (∀ (A : Set ℝ) (s : ℝ), 0 < s →
    GP.hausdorff s A = MeasureTheory.Measure.hausdorffMeasure s A)) (h_T002 : dimH E < ⊤ ∧ 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧
  (n = 0 → E = Set.univ ∧ (∃ x : GP.Space n, E = {x}) ∧ dimH E = 0) ∧
  ∀ (s δ : ℝ), 0 < s → 0 < δ → GP.content s δ E < ⊤) (h_T009 : ∀ (s δ : ℝ), 0 < s → 0 < δ →
  GP.content s δ E ≤ GP.content (s + 1) δ (GP.cylinder E)) :
    0 < dimH E → dimH E + 1 ≤ dimH (GP.cylinder E) := by
  intro hpos
  have hfin : dimH E ≠ ⊤ := h_T002.1.ne
  let D : ℝ := (dimH E).toReal
  have hD : 0 < D := ENNReal.toReal_pos_iff.2 ⟨hpos, h_T002.1⟩
  have hDcast : ENNReal.ofReal D = dimH E := ENNReal.ofReal_toReal hfin
  have hscale : ∀ (s δ η : ℝ), δ ≤ η → GP.content s η E ≤ GP.content s δ E := by
    intro s δ η hδη
    unfold GP.content
    refine le_iInf fun U => le_iInf fun hU => ?_
    have hUη : GP.Cover E η U :=
      ⟨hU.1, fun i => (hU.2 i).trans (ENNReal.ofReal_le_ofReal hδη)⟩
    exact iInf_le_of_le U (iInf_le_of_le hUη le_rfl)
  have F003 : ∀ s : ℝ, 0 < s → s < D →
      ENNReal.ofReal (s + 1) ≤ dimH (GP.cylinder E) := by
    intro s hs hsD
    have hs_dim : ENNReal.ofReal s < dimH E :=
      (ENNReal.ofReal_lt_iff_lt_toReal hs.le hfin).2 hsD
    have hHs : GP.hausdorff s E = ⊤ :=
      ((h_T001.1 n E).2 s hs).2.2.1 hs_dim
    have F001 : ∀ T : ℝ, 0 < T → ∀ ε : ℝ, 0 < ε →
        ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧ ENNReal.ofReal T < GP.content s δ E := by
      intro T hT ε hε
      have hlt : ENNReal.ofReal T < GP.hausdorff s E := by
        rw [hHs]
        exact ENNReal.ofReal_lt_top
      have hex : ∃ δ : ℝ, 0 < δ ∧ ENNReal.ofReal T < GP.content s δ E := by
        simpa only [GP.hausdorff, lt_iSup_iff, exists_prop] using hlt
      obtain ⟨δ, hδ, hbound⟩ := hex
      refine ⟨min δ ε, lt_min hδ hε, min_le_right _ _, ?_⟩
      exact hbound.trans_le (hscale s (min δ ε) δ (min_le_left _ _))
    have F002 : ∀ T : ℝ, 0 < T →
        ENNReal.ofReal T < GP.hausdorff (s + 1) (GP.cylinder E) := by
      intro T hT
      obtain ⟨δ, hδ, _, hbound⟩ := F001 T hT 1 zero_lt_one
      have hcover : GP.content s δ E ≤ GP.content (s + 1) δ (GP.cylinder E) :=
        h_T009 s δ hs hδ
      have hsup : GP.content (s + 1) δ (GP.cylinder E) ≤
          GP.hausdorff (s + 1) (GP.cylinder E) := by
        unfold GP.hausdorff
        exact le_iSup_of_le δ (le_iSup_of_le hδ le_rfl)
      exact hbound.trans_le (hcover.trans hsup)
    have hHF : GP.hausdorff (s + 1) (GP.cylinder E) = ⊤ := by
      by_contra hQ
      let Q := GP.hausdorff (s + 1) (GP.cylinder E)
      have hp : 0 < Q.toReal + 1 := by positivity
      have hlt : ENNReal.ofReal (Q.toReal + 1) < Q := F002 _ hp
      have hrev : Q < ENNReal.ofReal (Q.toReal + 1) :=
        (ENNReal.lt_ofReal_iff_toReal_lt hQ).2 (by linarith)
      exact lt_asymm hlt hrev
    have hs1 : 0 < s + 1 := by linarith
    exact ((h_T001.1 (n + 1) (GP.cylinder E)).2 (s + 1) hs1).2.2.2.2 hHF
  have hlim : ENNReal.ofReal (D + 1) ≤ dimH (GP.cylinder E) := by
    by_cases hQ : dimH (GP.cylinder E) = ⊤
    · simp [hQ]
    apply (ENNReal.ofReal_le_iff_le_toReal hQ).2
    apply le_of_forall_lt
    intro b hb
    have hm : max 0 (b - 1) < D := max_lt hD (by linarith)
    obtain ⟨s, hs, hsD⟩ := exists_between hm
    have hs0 : 0 < s := lt_of_le_of_lt (le_max_left _ _) hs
    have hbs : b < s + 1 := by
      have : b - 1 < s := lt_of_le_of_lt (le_max_right _ _) hs
      linarith
    exact hbs.trans_le ((ENNReal.ofReal_le_iff_le_toReal hQ).1 (F003 s hs0 hsD))
  simpa only [ENNReal.ofReal_add hD.le (by norm_num : (0 : ℝ) ≤ 1),
    hDcast, ENNReal.ofReal_one] using hlim

theorem T011 (n : ℕ) (E : Set (GP.Space n)) (h_H002 : E.Nonempty) (h_T001 : (∀ (m : ℕ) (A : Set (GP.Space m)), 0 ≤ dimH A ∧
  ∀ (s : ℝ), 0 < s →
    GP.hausdorff s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (dimH A < ENNReal.ofReal s → GP.hausdorff s A = 0) ∧
    (ENNReal.ofReal s < dimH A → GP.hausdorff s A = ⊤) ∧
    (GP.hausdorff s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GP.hausdorff s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) ∧ (∀ (A : Set ℝ) (s : ℝ), 0 < s →
    GP.hausdorff s A = MeasureTheory.Measure.hausdorffMeasure s A)) (h_T003 : dimH GP.unitInterval = 1 ∧
  (∀ a : ℝ, 1 < a → GP.hausdorff a GP.unitInterval = 0) ∧
  (∀ s : ℝ, 0 < s → s < 1 → GP.hausdorff s GP.unitInterval = ⊤)) :
    dimH E = 0 → (1 : ℝ≥0∞) ≤ dimH (GP.cylinder E) ∧
  (1 : ℝ≥0∞) = dimH E + 1 := by
  intro hzero
  obtain ⟨x, hx⟩ := h_H002
  have hf : Isometry (GP.join x) := by
    apply Isometry.of_dist_eq
    intro t u
    rw [EuclideanSpace.dist_eq]
    simp [GP.join, Fin.sum_univ_castSucc, Real.dist_eq, Real.sqrt_sq_eq_abs]
  have hmem : ∀ t ∈ GP.unitInterval, GP.join x t ∈ GP.cylinder E := by
    intro t ht
    constructor
    · simpa [GP.horizontal, GP.join] using hx
    · simpa [GP.vertical, GP.join] using ht
  have hmono : ∀ (s : ℝ), 0 < s →
      GP.hausdorff s GP.unitInterval ≤ GP.hausdorff s (GP.cylinder E) := by
    intro s hs
    have hc : ∀ δ : ℝ, GP.content s δ GP.unitInterval ≤ GP.content s δ (GP.cylinder E) := by
      intro δ
      unfold GP.content
      refine le_iInf fun V => le_iInf fun hV => ?_
      let W : ℕ → Set ℝ := fun i => GP.join x ⁻¹' V i
      have hd : ∀ i, Metric.ediam (W i) ≤ Metric.ediam (V i) := by
        intro i
        apply Metric.ediam_le
        intro t ht u hu
        rw [← hf.edist_eq t u]
        exact Metric.edist_le_ediam_of_mem ht hu
      have hW : GP.Cover GP.unitInterval δ W := by
        constructor
        · intro t ht
          obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hV.1 (hmem t ht))
          exact Set.mem_iUnion.mpr ⟨i, hi⟩
        · intro i
          exact (hd i).trans (hV.2 i)
      have hcost : GP.cost s W ≤ GP.cost s V := by
        unfold GP.cost
        apply ENNReal.tsum_le_tsum
        intro i
        refine iSup_le fun hne => ?_
        have hneV : (V i).Nonempty := by
          obtain ⟨t, ht⟩ := hne
          exact ⟨GP.join x t, ht⟩
        exact (ENNReal.rpow_le_rpow (hd i) hs.le).trans (le_iSup_of_le hneV le_rfl)
      have hleft : GP.content s δ GP.unitInterval ≤ GP.cost s W := by
        unfold GP.content
        exact iInf_le_of_le W (iInf_le_of_le hW le_rfl)
      exact hleft.trans hcost
    unfold GP.hausdorff
    refine iSup_le fun δ => iSup_le fun hδ => ?_
    exact (hc δ).trans (le_iSup_of_le δ (le_iSup_of_le hδ le_rfl))
  have hdim : ∀ s : ℝ, 0 < s → s < 1 →
      ENNReal.ofReal s ≤ dimH (GP.cylinder E) := by
    intro s hs hs1
    have hinf : GP.hausdorff s (GP.cylinder E) = ⊤ := by
      apply top_unique
      rw [← h_T003.2.2 s hs hs1]
      exact hmono s hs
    exact (h_T001.1 (n + 1) (GP.cylinder E)).2 s hs |>.2.2.2.2 hinf
  constructor
  · apply ENNReal.le_of_forall_pos_nnreal_lt
    intro r hr hr1
    have hrpos : 0 < (r : ℝ) := by exact_mod_cast hr
    have hrlt : (r : ℝ) < 1 := by exact_mod_cast hr1
    have hconv : ENNReal.ofReal (r : ℝ) = (r : ℝ≥0∞) :=
      ENNReal.ofReal_coe_nnreal
    rw [← hconv]
    exact hdim (r : ℝ) hrpos hrlt
  · simp [hzero]

theorem T012 (n : ℕ) (E : Set (GP.Space n)) (h_T002 : dimH E < ⊤ ∧ 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧
  (n = 0 → E = Set.univ ∧ (∃ x : GP.Space n, E = {x}) ∧ dimH E = 0) ∧
  ∀ (s δ : ℝ), 0 < s → 0 < δ → GP.content s δ E < ⊤) (h_T006 : dimH (GP.cylinder E) ≤ dimH E + 1 ∧ dimH (GP.cylinder E) < ⊤) (h_T010 : 0 < dimH E → dimH E + 1 ≤ dimH (GP.cylinder E)) (h_T011 : dimH E = 0 → (1 : ℝ≥0∞) ≤ dimH (GP.cylinder E) ∧
  (1 : ℝ≥0∞) = dimH E + 1) :
    dimH (GP.cylinder E) = dimH E + 1 := by
  apply le_antisymm h_T006.1
  by_cases hD : dimH E = 0
  · have h := h_T011 hD
    exact h.2 ▸ h.1
  · exact h_T010 (lt_of_le_of_ne h_T002.2.1 (Ne.symm hD))

set_option Elab.async false in
theorem P (n : ℕ) (E : Set (GP.Space n)) (h_H001 : 0 ≤ n) (h_H002 : E.Nonempty) (h_H003 : IsCompact E) :
    dimH (GP.cylinder E) = dimH E + 1 := by
  have h_T001 : (∀ (m : ℕ) (A : Set (GP.Space m)), 0 ≤ dimH A ∧
  ∀ (s : ℝ), 0 < s →
    GP.hausdorff s A = MeasureTheory.Measure.hausdorffMeasure s A ∧
    (dimH A < ENNReal.ofReal s → GP.hausdorff s A = 0) ∧
    (ENNReal.ofReal s < dimH A → GP.hausdorff s A = ⊤) ∧
    (GP.hausdorff s A = 0 → dimH A ≤ ENNReal.ofReal s) ∧
    (GP.hausdorff s A = ⊤ → ENNReal.ofReal s ≤ dimH A)) ∧ (∀ (A : Set ℝ) (s : ℝ), 0 < s →
    GP.hausdorff s A = MeasureTheory.Measure.hausdorffMeasure s A) := @T001 n E 
  have h_T002 : dimH E < ⊤ ∧ 0 ≤ dimH E ∧ dimH E ≤ (n : ℝ≥0∞) ∧
  (n = 0 → E = Set.univ ∧ (∃ x : GP.Space n, E = {x}) ∧ dimH E = 0) ∧
  ∀ (s δ : ℝ), 0 < s → 0 < δ → GP.content s δ E < ⊤ := @T002 n E h_H001 h_H002 h_H003 h_T001
  have h_T003 : dimH GP.unitInterval = 1 ∧
  (∀ a : ℝ, 1 < a → GP.hausdorff a GP.unitInterval = 0) ∧
  (∀ s : ℝ, 0 < s → s < 1 → GP.hausdorff s GP.unitInterval = ⊤) := @T003 n E h_T001
  have h_T004 : n = 0 → dimH (GP.cylinder E) ≤ dimH E + 1 := @T004 n E h_T001 h_T002 h_T003
  have h_T005 : 1 ≤ n → ∀ (q : ℝ), dimH E < ENNReal.ofReal q →
  ∀ (δ ε : ℝ), 0 < δ → 0 < ε →
    GP.content (q + 1) δ (GP.cylinder E) ≤
      ENNReal.ofReal (2 * (Real.sqrt 2) ^ (q + 1) * ε) := @T005 n E h_T001 h_T002
  have h_T006 : dimH (GP.cylinder E) ≤ dimH E + 1 ∧ dimH (GP.cylinder E) < ⊤ := @T006 n E h_T001 h_T002 h_T004 h_T005
  have h_T007 : ∀ (s δ : ℝ), 0 < s → 0 < δ →
  ∀ (V : ℕ → Set (GP.Space (n + 1))), GP.Cover (GP.cylinder E) δ V →
  ∀ ε : ℝ, 0 < ε → ∃ J : ℕ → Set ℝ,
    (∀ i, IsOpen (J i)) ∧
    (∀ i, GP.vertical '' (V i) ⊆ J i) ∧
    (∀ i, MeasureTheory.volume (J i) ≤ Metric.ediam (V i) +
      ENNReal.ofReal (ε * (1 / 2 : ℝ) ^ (i + 1) /
        (1 + (Metric.diam (V i)) ^ s))) ∧
    (∀ t ∈ GP.unitInterval,
      GP.content s δ E ≤
        ∑' i, (J i).indicator (fun _ => (Metric.ediam (V i)) ^ s) t) := @T007 n E h_T002
  have h_T008 : ∀ (s δ : ℝ), 0 < s → 0 < δ →
  ∀ (V : ℕ → Set (GP.Space (n + 1))), GP.Cover (GP.cylinder E) δ V →
  ∀ ε : ℝ, 0 < ε →
    GP.content s δ E ≤ GP.cost (s + 1) V + ENNReal.ofReal ε := @T008 n E h_T002 h_T007
  have h_T009 : ∀ (s δ : ℝ), 0 < s → 0 < δ →
  GP.content s δ E ≤ GP.content (s + 1) δ (GP.cylinder E) := @T009 n E h_T008
  have h_T010 : 0 < dimH E → dimH E + 1 ≤ dimH (GP.cylinder E) := @T010 n E h_T001 h_T002 h_T009
  have h_T011 : dimH E = 0 → (1 : ℝ≥0∞) ≤ dimH (GP.cylinder E) ∧
  (1 : ℝ≥0∞) = dimH E + 1 := @T011 n E h_H002 h_T001 h_T003
  have h_T012 : dimH (GP.cylinder E) = dimH E + 1 := @T012 n E h_T002 h_T006 h_T010 h_T011
  exact h_T012

#check @P
#print axioms P

end Translation
