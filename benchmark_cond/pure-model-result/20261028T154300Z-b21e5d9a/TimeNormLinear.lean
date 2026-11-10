import Proof
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

theorem timeLInfinity_sub_le {s a b : ℝ} {f g : ℝ → Sobolev s}
    (hf : MemLp f ∞ (volume.restrict (Set.Icc a b)))
    (hg : MemLp g ∞ (volume.restrict (Set.Icc a b))) :
    timeLInfinity a b (fun t => f t - g t) ≤ timeLInfinity a b f + timeLInfinity a b g := by
  apply timeLInfinity_le_of_ae_bound (add_nonneg (timeLInfinity_nonneg _ _ _) (timeLInfinity_nonneg _ _ _))
  filter_upwards [timeLInfinity_ae_bound hf, timeLInfinity_ae_bound hg] with t ht ht'
  exact (norm_sub_le _ _).trans (add_le_add ht ht')

theorem timeLInfinity_smul_le {s a b : ℝ} {f : ℝ → Sobolev s}
    (hf : MemLp f ∞ (volume.restrict (Set.Icc a b))) (z : ℂ) :
    timeLInfinity a b (fun t => z • f t) ≤ ‖z‖ * timeLInfinity a b f := by
  apply timeLInfinity_le_of_ae_bound (mul_nonneg (norm_nonneg _) (timeLInfinity_nonneg _ _ _))
  filter_upwards [timeLInfinity_ae_bound hf] with t ht
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left ht (norm_nonneg _)

theorem timeXNorm_affine_le {a b : ℝ} {f g : ℝ → Sobolev 0} {df dg : ℝ → Sobolev (-pStar)}
    (hf : MemLp f ∞ (volume.restrict (Set.Icc a b))) (hg : MemLp g ∞ (volume.restrict (Set.Icc a b)))
    (hdf : MemLp df ∞ (volume.restrict (Set.Icc a b))) (hdg : MemLp dg ∞ (volume.restrict (Set.Icc a b))) (z : ℂ) :
    timeXNorm a b (fun t => f t - z • g t) (fun t => df t - z • dg t) ≤
      timeXNorm a b f df + ‖z‖ * timeXNorm a b g dg := by
  have h0 := timeLInfinity_sub_le hf (hg.const_smul z)
  have hd0 := timeLInfinity_sub_le hdf (hdg.const_smul z)
  have hs := timeLInfinity_smul_le hg z
  have hds := timeLInfinity_smul_le hdg z
  change timeLInfinity a b (fun t => f t - z • g t) + timeLInfinity a b (fun t => df t - z • dg t) ≤ _
  calc
    _ ≤ (timeLInfinity a b f + ‖z‖ * timeLInfinity a b g) +
        (timeLInfinity a b df + ‖z‖ * timeLInfinity a b dg) :=
      add_le_add (h0.trans (add_le_add le_rfl hs)) (hd0.trans (add_le_add le_rfl hds))
    _ = _ := by unfold timeXNorm; ring

def exactL2Path {T : ℝ} {u0 : Fourier} {u : ℝ → Fourier}
    (hT : 0 ≤ T) (hu : KdVSolution 2 T u0 u) (t : ℝ) : Sobolev 0 :=
  inclusionMap 0 2 (by norm_num) (extendedTwistedPath hT hu t)

def exactNegativeDerivative {T : ℝ} {u0 : Fourier} {u : ℝ → Fourier}
    (hT : 0 ≤ T) (hu : KdVSolution 2 T u0 u) (t : ℝ) : Sobolev (-pStar) :=
  inclusionMap (-pStar) 1 (by norm_num [pStar]) (exactTwistedDerivative hT hu t)

theorem exactL2Path_bound {T γ M : ℝ} {u0 : Fourier} {u : ℝ → Fourier}
    (hT : 0 ≤ T) (hγ : 0 ≤ γ) (hγ2 : γ ≤ 2) (hu : KdVSolution 2 T u0 u)
    (hM : ∀ t ∈ Set.Icc 0 T, hNorm γ (u t) ≤ M) (r : ℝ) : ‖exactL2Path hT hu r‖ ≤ M := by
  rw [sobolev_norm]
  exact (hNorm_mono ((extendedTwistedPath hT hu r).property.of_le hγ2) hγ).trans
    (extendedTwistedPath_bound hT hu hM r)

theorem exact_time_bounds {T γ M : ℝ} {u0 : Fourier} {u : ℝ → Fourier}
    (hT : 0 ≤ T) (hγ : 0 ≤ γ) (hγ2 : γ ≤ 2) (hM : 0 ≤ M) (hu : KdVSolution 2 T u0 u)
    (huM : ∀ t ∈ Set.Icc 0 T, hNorm γ (u t) ≤ M) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) :
    MemLp (exactL2Path hT hu) ∞ (volume.restrict (Set.Icc a b)) ∧
    MemLp (exactNegativeDerivative hT hu) ∞ (volume.restrict (Set.Icc a b)) ∧
    WeakTimeDerivative a b (fun t => (exactL2Path hT hu t).val) (fun t => (exactNegativeDerivative hT hu t).val) ∧
    timeXNorm a b (exactL2Path hT hu) (exactNegativeDerivative hT hu) ≤
      M + (1 / 2 : ℝ) * negativeProductConstant (9 / 14) (by norm_num) * M ^ 2 := by
  let K := negativeProductConstant (9 / 14) (by norm_num)
  have hK : 0 ≤ K := norm_nonneg _
  have hfC : Continuous (exactL2Path hT hu) :=
    (inclusionMap 0 2 (by norm_num)).continuous.comp (continuous_extendedTwistedPath hT hu)
  have hdfC : Continuous (exactNegativeDerivative hT hu) :=
    (inclusionMap (-pStar) 1 (by norm_num [pStar])).continuous.comp (continuous_exactTwistedDerivative hT hu)
  refine ⟨continuousOn_memLp_top_Icc hfC.continuousOn, continuousOn_memLp_top_Icc hdfC.continuousOn, ?_, ?_⟩
  · have hvc : Continuous (exactTwistedOne hT hu) :=
      (inclusionMap 1 2 (by norm_num)).continuous.comp (continuous_extendedTwistedPath hT hu)
    have hreg := regularFourierPath_of_bundled (a := a) (b := b) hvc (continuous_exactTwistedDerivative hT hu)
      (fun t ht k => extendedTwistedPath_hasDerivAt hT hu
        ⟨lt_of_le_of_lt ha ht.1, lt_of_lt_of_le ht.2 hb⟩ k)
    exact hreg.weakTimeDerivative hab
  · have hfb : timeLInfinity a b (exactL2Path hT hu) ≤ M := timeLInfinity_le_of_bound hM _
      (fun t _ => exactL2Path_bound hT hγ hγ2 hu huM t)
    have hdfb : timeLInfinity a b (exactNegativeDerivative hT hu) ≤ (1 / 2 : ℝ) * K * M ^ 2 := by
      apply timeLInfinity_le_of_bound (by positivity)
      intro t _
      have hf0 := (extendedTwistedPath hT hu t).property.of_le (by norm_num : (0 : ℝ) ≤ 2)
      obtain ⟨hB, hBn⟩ := B_negative_bound hf0 hf0 t
      have hvM : hNorm 0 (extendedTwistedPath hT hu t).val ≤ M := by
        simpa only [sobolev_norm, exactL2Path, inclusionMap_val] using exactL2Path_bound hT hγ hγ2 hu huM t
      rw [sobolev_norm]
      change hNorm (-pStar) (exactTwistedDerivative hT hu t).val ≤ _
      rw [exactTwistedDerivative_equation, hNorm_smul hB]
      have hhalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
      rw [hhalf]
      have hv0 := hNorm_nonneg 0 (extendedTwistedPath hT hu t).val
      calc
        _ ≤ (1 / 2 : ℝ) * (K * hNorm 0 (extendedTwistedPath hT hu t).val * hNorm 0 (extendedTwistedPath hT hu t).val) :=
          mul_le_mul_of_nonneg_left hBn (by norm_num)
        _ ≤ (1 / 2 : ℝ) * (K * M * M) := by gcongr
        _ = _ := by ring
    exact add_le_add hfb hdfb

end KdV
