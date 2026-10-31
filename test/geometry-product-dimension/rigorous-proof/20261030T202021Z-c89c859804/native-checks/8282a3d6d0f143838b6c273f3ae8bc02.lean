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

namespace Translation
set_option autoImplicit false

theorem T016 (n : ℕ) (E : Set (GPEucl n)) (h_T002 : (∀ (k : ℕ) (A : Set (GPEucl k)) (s : ℝ), 0 < s →
    GPmass s A = MeasureTheory.Measure.hausdorffMeasure s A) ∧
  (∀ (A : Set ℝ) (s : ℝ), 0 < s →
    GPmass s A = MeasureTheory.Measure.hausdorffMeasure s A)) (h_T014 : dimH GPI ≤ 1 ∧ ∀ a : ℝ, 1 < a → GPmass a GPI = 0) (h_T015 : ∀ (δ : ℝ) (U : ℕ → Set ℝ), 0 < δ →
  GPcover GPI δ U → (1 : ENNReal) ≤ ∑' i, Metric.ediam (U i)) :
    dimH GPI = 1 ∧
  ∀ s : ℝ, 0 < s → s < 1 → GPmass s GPI = ⊤ := by
  have hreal : ∀ (s δ ρ : ℝ), 0 < s → s < 1 → 0 < δ →
      0 ≤ ρ → ρ ≤ δ → δ ^ (s - 1) * ρ ≤ ρ ^ s := by
    intro s δ ρ hs hs1 hδ hρ hρδ
    by_cases hzero : ρ = 0
    · subst ρ
      simp [Real.zero_rpow (ne_of_gt hs)]
    · have hpos : 0 < ρ := lt_of_le_of_ne hρ (Ne.symm hzero)
      calc
        δ ^ (s - 1) * ρ ≤ ρ ^ (s - 1) * ρ :=
          mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow_of_nonpos hpos hρδ (by linarith)) hρ
        _ = ρ ^ s := by simpa using (Real.rpow_add hpos (s - 1) 1).symm
  have hterm : ∀ (s δ : ℝ) (d : ENNReal), 0 < s → s < 1 →
      0 < δ → d ≤ ENNReal.ofReal δ →
      ENNReal.ofReal (δ ^ (s - 1)) * d ≤ d ^ s := by
    intro s δ d hs hs1 hδ hd
    have hdtop : d ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hd
    have hconv : ENNReal.ofReal d.toReal = d := ENNReal.ofReal_toReal hdtop
    have hpow : d ^ s = ENNReal.ofReal (d.toReal ^ s) := by
      calc
        d ^ s = (ENNReal.ofReal d.toReal) ^ s :=
          congrArg (fun x : ENNReal => x ^ s) hconv.symm
        _ = _ := ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hs.le
    calc
      ENNReal.ofReal (δ ^ (s - 1)) * d =
          ENNReal.ofReal (δ ^ (s - 1) * d.toReal) := by
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _), hconv]
      _ ≤ ENNReal.ofReal (d.toReal ^ s) :=
        ENNReal.ofReal_le_ofReal (hreal s δ d.toReal hs hs1 hδ
          ENNReal.toReal_nonneg (ENNReal.toReal_le_of_le_ofReal hδ.le hd))
      _ = d ^ s := hpow.symm
  have hinfinite : ∀ s : ℝ, 0 < s → s < 1 → GPmass s GPI = ⊤ := by
    intro s hs hs1
    have hcontent : ∀ δ : ℝ, 0 < δ →
        ENNReal.ofReal (δ ^ (s - 1)) ≤ GPcontent s δ GPI := by
      intro δ hδ
      unfold GPcontent
      refine le_iInf fun U => le_iInf fun hU => ?_
      calc
        ENNReal.ofReal (δ ^ (s - 1)) =
            ENNReal.ofReal (δ ^ (s - 1)) * 1 := (mul_one _).symm
        _ ≤ ENNReal.ofReal (δ ^ (s - 1)) * ∑' i, Metric.ediam (U i) :=
          mul_le_mul_left' (h_T015 δ U hδ hU) _
        _ = ∑' i, ENNReal.ofReal (δ ^ (s - 1)) * Metric.ediam (U i) :=
          ENNReal.tsum_mul_left.symm
        _ ≤ GPcost s U :=
          ENNReal.tsum_le_tsum (fun i => hterm s δ (Metric.ediam (U i)) hs hs1 hδ (hU.2 i))
    have hbound : ∀ δ : ℝ, 0 < δ →
        ENNReal.ofReal (δ ^ (s - 1)) ≤ GPmass s GPI := by
      intro δ hδ
      exact (hcontent δ hδ).trans (le_iSup_of_le δ (le_iSup_of_le hδ le_rfl))
    have hlim : Filter.Tendsto (fun δ : ℝ => ENNReal.ofReal (δ ^ (s - 1)))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (⊤ : ENNReal)) :=
      ENNReal.tendsto_ofReal_atTop.comp
        (tendsto_rpow_neg_nhdsGT_zero (by linarith : s - 1 < 0))
    apply top_unique
    apply le_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact hbound δ hδ
  refine ⟨le_antisymm h_T014.1 ?_, hinfinite⟩
  apply le_of_not_gt
  intro hlt
  obtain ⟨s, hs0, hds, hs1⟩ := ENNReal.lt_iff_exists_real_btwn.mp hlt
  have hs : 0 < s := ENNReal.ofReal_pos.mp (lt_of_le_of_lt bot_le hds)
  have hsone : s < 1 := by
    have : ENNReal.ofReal s < ENNReal.ofReal 1 := by simpa using hs1
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mp this
  have hm : MeasureTheory.Measure.hausdorffMeasure s GPI = ⊤ :=
    (h_T002.2 GPI s hs).symm.trans (hinfinite s hs hsone)
  have hscoe : (s.toNNReal : ℝ) = s := by
    simp [Real.toNNReal_of_nonneg hs.le]
  have hn : MeasureTheory.Measure.hausdorffMeasure (s.toNNReal : ℝ) GPI = ⊤ := by
    rwa [hscoe]
  have hle : ENNReal.ofReal s ≤ dimH GPI :=
    le_dimH_of_hausdorffMeasure_eq_top (d := s.toNNReal) hn
  exact (not_lt_of_ge hle) hds

#check @T016
#print axioms T016

end Translation
