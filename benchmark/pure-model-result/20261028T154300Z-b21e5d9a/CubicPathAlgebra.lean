import ProjectionSupport
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

def COneBundled (t : ℝ) (f g h : Sobolev 1) : Sobolev 1 :=
  airyMap 1 (-t) (removeMeanMap 1 (productMap
    (removeMeanMap 1 (productMap (airyMap 1 t f) (airyMap 1 t g)))
    (airyMap 1 t (inverseDerivativeSameMap 1 h))))

theorem COneBundled_val (t : ℝ) (f g h : Sobolev 1) :
    (COneBundled t f g h).val = CIntegrand t f.val g.val h.val := rfl

theorem continuous_COneBundled {X : Type*} [TopologicalSpace X]
    {t : X → ℝ} {f g h : X → Sobolev 1} (ht : Continuous t)
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) :
    Continuous (fun x => COneBundled (t x) (f x) (g x) (h x)) := by
  unfold COneBundled
  have hF := continuous_airy_apply 1 ht hf
  have hG := continuous_airy_apply 1 ht hg
  have hH := continuous_airy_apply 1 ht ((inverseDerivativeSameMap 1).continuous.comp hh)
  apply continuous_airy_apply 1 ht.neg
  fun_prop

theorem continuous_CIntegrand_paths {f g h : ℝ → Sobolev 1}
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) (k : ℤ) :
    Continuous (fun t : ℝ => CIntegrand t (f t).val (g t).val (h t).val k) := by
  have hc := (coefficientMap 1 k).continuous.comp (continuous_COneBundled continuous_id hf hg hh)
  simpa only [Function.comp_def, coefficientMap_apply, COneBundled_val, id_eq] using hc

def CIntegralPathBundled (a b : ℝ) (f g h : ℝ → Sobolev 1) : Sobolev 1 :=
  ∫ t : ℝ in a..b, COneBundled t (f t) (g t) (h t)

theorem CIntegralPathBundled_val (a b : ℝ) {f g h : ℝ → Sobolev 1}
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) :
    (CIntegralPathBundled a b f g h).val =
      CIntegral a b (fun t => (f t).val) (fun t => (g t).val) (fun t => (h t).val) := by
  exact sobolev_integral_val ((continuous_COneBundled continuous_id hf hg hh).intervalIntegrable a b)

theorem CIntegral_comm (a b : ℝ) (f g h : ℝ → Fourier) : CIntegral a b f g h = CIntegral a b g f h := by
  funext k
  simp_rw [CIntegral_eq_integrand, CIntegrand_comm]

theorem CIntegral_paths_add_left (a b : ℝ) {f l g h : ℝ → Sobolev 1}
    (hf : Continuous f) (hl : Continuous l) (hg : Continuous g) (hh : Continuous h) :
    CIntegral a b (fun t => ((f + l) t).val) (fun t => (g t).val) (fun t => (h t).val) =
      CIntegral a b (fun t => (f t).val) (fun t => (g t).val) (fun t => (h t).val) +
      CIntegral a b (fun t => (l t).val) (fun t => (g t).val) (fun t => (h t).val) := by
  funext k
  have heq (t : ℝ) : CIntegrand t ((f + l) t).val (g t).val (h t).val =
      CIntegrand t (f t).val (g t).val (h t).val + CIntegrand t (l t).val (g t).val (h t).val :=
    CIntegrand_add_left ((f t).property.of_le (by norm_num)) ((l t).property.of_le (by norm_num))
      ((g t).property.of_le (by norm_num)) ((h t).property.of_le (by norm_num)) t
  simp_rw [CIntegral_eq_integrand, heq, Pi.add_apply]
  exact intervalIntegral.integral_add ((continuous_CIntegrand_paths hf hg hh k).intervalIntegrable a b)
    ((continuous_CIntegrand_paths hl hg hh k).intervalIntegrable a b)

theorem CIntegral_paths_sub_left (a b : ℝ) {f l g h : ℝ → Sobolev 1}
    (hf : Continuous f) (hl : Continuous l) (hg : Continuous g) (hh : Continuous h) :
    CIntegral a b (fun t => ((f - l) t).val) (fun t => (g t).val) (fun t => (h t).val) =
      CIntegral a b (fun t => (f t).val) (fun t => (g t).val) (fun t => (h t).val) -
      CIntegral a b (fun t => (l t).val) (fun t => (g t).val) (fun t => (h t).val) := by
  have heq := CIntegral_paths_add_left a b (hf.sub hl) hl hg hh
  simp only [sub_add_cancel] at heq
  exact eq_sub_iff_add_eq.mpr heq.symm

theorem CIntegral_paths_sub_middle (a b : ℝ) {f g l h : ℝ → Sobolev 1}
    (hf : Continuous f) (hg : Continuous g) (hl : Continuous l) (hh : Continuous h) :
    CIntegral a b (fun t => (f t).val) (fun t => ((g - l) t).val) (fun t => (h t).val) =
      CIntegral a b (fun t => (f t).val) (fun t => (g t).val) (fun t => (h t).val) -
      CIntegral a b (fun t => (f t).val) (fun t => (l t).val) (fun t => (h t).val) := by
  rw [CIntegral_comm a b _ (fun t => ((g - l) t).val), CIntegral_paths_sub_left a b hg hl hf hh,
    CIntegral_comm a b (fun t => (g t).val), CIntegral_comm a b (fun t => (l t).val)]

theorem CIntegral_paths_add_right (a b : ℝ) {f g h l : ℝ → Sobolev 1}
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) (hl : Continuous l) :
    CIntegral a b (fun t => (f t).val) (fun t => (g t).val) (fun t => ((h + l) t).val) =
      CIntegral a b (fun t => (f t).val) (fun t => (g t).val) (fun t => (h t).val) +
      CIntegral a b (fun t => (f t).val) (fun t => (g t).val) (fun t => (l t).val) := by
  funext k
  have heq (t : ℝ) : CIntegrand t (f t).val (g t).val ((h + l) t).val =
      CIntegrand t (f t).val (g t).val (h t).val + CIntegrand t (f t).val (g t).val (l t).val :=
    CIntegrand_add_right ((f t).property.of_le (by norm_num)) ((g t).property.of_le (by norm_num))
      ((h t).property.of_le (by norm_num)) ((l t).property.of_le (by norm_num)) t
  simp_rw [CIntegral_eq_integrand, heq, Pi.add_apply]
  exact intervalIntegral.integral_add ((continuous_CIntegrand_paths hf hg hh k).intervalIntegrable a b)
    ((continuous_CIntegrand_paths hf hg hl k).intervalIntegrable a b)

theorem CIntegral_paths_sub_right (a b : ℝ) {f g h l : ℝ → Sobolev 1}
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) (hl : Continuous l) :
    CIntegral a b (fun t => (f t).val) (fun t => (g t).val) (fun t => ((h - l) t).val) =
      CIntegral a b (fun t => (f t).val) (fun t => (g t).val) (fun t => (h t).val) -
      CIntegral a b (fun t => (f t).val) (fun t => (g t).val) (fun t => (l t).val) := by
  have heq := CIntegral_paths_add_right a b hf hg (hh.sub hl) hl
  simp only [sub_add_cancel] at heq
  exact eq_sub_iff_add_eq.mpr heq.symm

theorem CIntegral_paths_difference (a b : ℝ) {f g h F G H : ℝ → Sobolev 1}
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h)
    (hF : Continuous F) (hG : Continuous G) (hH : Continuous H) :
    CIntegral a b (fun t => (f t).val) (fun t => (g t).val) (fun t => (h t).val) -
      CIntegral a b (fun t => (F t).val) (fun t => (G t).val) (fun t => (H t).val) =
      CIntegral a b (fun t => ((f - F) t).val) (fun t => (g t).val) (fun t => (h t).val) +
      CIntegral a b (fun t => (F t).val) (fun t => ((g - G) t).val) (fun t => (h t).val) +
      CIntegral a b (fun t => (F t).val) (fun t => (G t).val) (fun t => ((h - H) t).val) := by
  rw [CIntegral_paths_sub_left a b hf hF hg hh, CIntegral_paths_sub_middle a b hF hg hG hh,
    CIntegral_paths_sub_right a b hF hG hh hH]
  abel

end KdV
