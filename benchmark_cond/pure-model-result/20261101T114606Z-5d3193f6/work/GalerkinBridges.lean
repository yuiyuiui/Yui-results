import OriginalExternals
noncomputable section
open scoped ENNReal
open MeasureTheory KdV
namespace BareModelCompletion

/-- Only finitely many modes move. Source H0 continuity therefore preserves
every higher initial Sobolev regularity; no new source assumption is used. -/
theorem galerkin_higher_continuity {s T : ℝ} (hs : 0 ≤ s) {m : ℕ}
    {f : Fourier} (hf : InHomSobolev s f) {v : ℝ → Fourier}
    (hc : HomSobolevContinuousOn 0 T v) (hv : SourceGalerkinODE m T f v) :
    HomSobolevContinuousOn s T v := by
  have htail (t : ℝ) (ht : t ∈ Set.Icc 0 T) := hv.tail_stationary (le_refl (0 : ℝ)) hc ht
  have hlow (t : ℝ) (ht : t ∈ Set.Icc 0 T) : InHomSobolev s (cutoff m (v t)) :=
    (cutoff_inSobolev_all s m (v t)).to_homogeneous hs (cutoff_meanZero (hc.1 t ht).1 m)
  have hmem (t : ℝ) (ht : t ∈ Set.Icc 0 T) : InHomSobolev s (v t) := by
    have he : v t = cutoff m (v t) + highCutoff m f := by
      rw [← htail t ht]
      unfold highCutoff
      abel
    rw [he]
    exact (hlow t ht).add (hf.sub (hf.cutoff m))
  refine ⟨hmem, ?_⟩
  intro t ht ε hε
  obtain ⟨δ, hδ, hd⟩ := hc.2 t ht (ε / weight s (m : ℤ)) (div_pos hε (weight_pos _ _))
  refine ⟨δ, hδ, ?_⟩
  intro r hr hrt
  have he : v r - v t = cutoff m (v r - v t) := by
    rw [cutoff_sub]
    calc
      _ = (cutoff m (v r) + highCutoff m (v r)) -
          (cutoff m (v t) + highCutoff m (v t)) := by unfold highCutoff; abel
      _ = _ := by rw [htail r hr, htail t ht]; abel
  have hD : InHomSobolev 0 (v r - v t) := (hc.1 r hr).sub (hc.1 t ht)
  have hg := cutoff_gain_bound hs (hD.to_inhomogeneous (le_refl 0)) m
  simp only [zero_add] at hg
  have hn := homogeneousNorm_le_hNorm hs hg.1 (cutoff_meanZero hD.1 m)
  have hb : homogeneousNorm s (v r - v t) ≤ weight s (m : ℤ) * homogeneousNorm 0 (v r - v t) := by
    calc
      _ = homogeneousNorm s (cutoff m (v r - v t)) := congrArg (homogeneousNorm s) he
      _ ≤ hNorm s (cutoff m (v r - v t)) := hn
      _ ≤ _ := by simpa only [homogeneousNorm_zero] using hg.2
  have hh := mul_lt_mul_of_pos_left (hd r hr hrt) (weight_pos s (m : ℤ))
  have heps : weight s (m : ℤ) * (ε / weight s (m : ℤ)) = ε := by
    field_simp [(weight_pos s (m : ℤ)).ne']
  rw [heps] at hh
  exact hb.trans_lt hh

theorem source_galerkin_family (h41 : BITProposition41) {s T : ℝ}
    (hs : 0 ≤ s) (hT : 0 < T) (f : Fourier) (hfr : RealValued f) (hf : InHomSobolev s f) :
    ∃ G : ℕ → ℝ → Fourier, ∀ m, HomSobolevContinuousOn s T (G m) ∧
      (∀ t ∈ Set.Icc 0 T, RealValued (G m t)) ∧ SourceGalerkinODE (m + 1) T f (G m) := by
  choose G hG hEnergy using (fun m : ℕ => h41 f hfr (hf.of_le hs) (m + 1) (by omega))
  refine ⟨G, ?_⟩
  intro m
  obtain ⟨hc, hr, hODE⟩ := hG m T hT
  exact ⟨galerkin_higher_continuity hs hf hc hODE, hr, hODE⟩


/-- Two directions of the source Galerkin solution-class correspondence. -/
theorem galerkin_continuity_iff {s T : ℝ} (hs : 0 ≤ s) {m : ℕ}
    {f : Fourier} (hf : InHomSobolev s f) {v : ℝ → Fourier}
    (hv : SourceGalerkinODE m T f v) :
    HomSobolevContinuousOn s T v ↔ HomSobolevContinuousOn 0 T v :=
  ⟨fun hc => hc.of_le hs, fun hc => galerkin_higher_continuity hs hf hc hv⟩


/-- Solving the source Fourier sum constraint does not change its index domain. -/
def tripleSumEquiv (k : ℤ) : (ℤ × ℤ) ≃
    {q : ℤ × ℤ × ℤ // q.1 + q.2.1 + q.2.2 = k} where
  toFun q := ⟨(q.1, q.2, k - q.1 - q.2), by dsimp; omega⟩
  invFun q := (q.val.1, q.val.2.1)
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨a, b, c⟩, h⟩
    apply Subtype.ext
    dsimp only
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · dsimp at h ⊢
        omega

def quadrupleSumEquiv (k : ℤ) : (ℤ × ℤ × ℤ) ≃
    {q : ℤ × ℤ × ℤ × ℤ // q.1 + q.2.1 + q.2.2.1 + q.2.2.2 = k} where
  toFun q := ⟨(q.1, q.2.1, q.2.2, k - q.1 - q.2.1 - q.2.2), by dsimp; omega⟩
  invFun q := (q.val.1, q.val.2.1, q.val.2.2.1)
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨a, b, c, d⟩, h⟩
    apply Subtype.ext
    dsimp only
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · apply Prod.ext
        · rfl
        · dsimp at h ⊢
          omega

theorem triple_tsum_reindex (k : ℤ)
    (F : {q : ℤ × ℤ × ℤ // q.1 + q.2.1 + q.2.2 = k} → ℂ) :
    (∑' q : ℤ × ℤ, F (tripleSumEquiv k q)) = ∑' q, F q :=
  (tripleSumEquiv k).tsum_eq F

theorem quadruple_tsum_reindex (k : ℤ)
    (F : {q : ℤ × ℤ × ℤ × ℤ // q.1 + q.2.1 + q.2.2.1 + q.2.2.2 = k} → ℂ) :
    (∑' q : ℤ × ℤ × ℤ, F (quadrupleSumEquiv k q)) = ∑' q, F q :=
  (quadrupleSumEquiv k).tsum_eq F

theorem nonresonant_zero_denominator {ι : Type*} (N D : ι → ℂ) :
    (∑' q, N q / D q) = ∑' q, if D q = 0 then 0 else N q / D q := by
  apply tsum_congr
  intro q
  by_cases hq : D q = 0 <;> simp [hq]

theorem cubic_zero_input (f g h : Fourier) (hf : MeanZero f) (hg : MeanZero g) (hh : MeanZero h)
    (a b c : ℤ) (hz : a = 0 ∨ b = 0 ∨ c = 0) (E D : ℂ) :
    E * f a * g b * h c / D = 0 := by
  have hf0 : f 0 = 0 := hf
  have hg0 : g 0 = 0 := hg
  have hh0 : h 0 = 0 := hh
  rcases hz with hz | hz | hz <;> simp [hz, hf0, hg0, hh0]

theorem quartic_zero_input (f g h q : Fourier)
    (hf : MeanZero f) (hg : MeanZero g) (hh : MeanZero h) (hq : MeanZero q)
    (a b c d : ℤ) (hz : a = 0 ∨ b = 0 ∨ c = 0 ∨ d = 0) (E D : ℂ) :
    E * f a * g b * h c * q d / D = 0 := by
  have hf0 : f 0 = 0 := hf
  have hg0 : g 0 = 0 := hg
  have hh0 : h 0 = 0 := hh
  have hq0 : q 0 = 0 := hq
  rcases hz with hz | hz | hz | hz <;> simp [hz, hf0, hg0, hh0, hq0]


@[simp] theorem bitB2_zero (t : ℝ) (f g : Fourier) : bitB2 t f g 0 = 0 := by simp [bitB2]
@[simp] theorem bitB3_zero (t : ℝ) (f g h : Fourier) : bitB3 t f g h 0 = 0 := by simp [bitB3]
@[simp] theorem bitB14_zero (t : ℝ) (f g h q : Fourier) : bitB14 t f g h q 0 = 0 := by simp [bitB14]
@[simp] theorem bitB24_zero (t : ℝ) (f g h q : Fourier) : bitB24 t f g h q 0 = 0 := by simp [bitB24]
@[simp] theorem bitB4_zero (t : ℝ) (f g h q : Fourier) : bitB4 t f g h q 0 = 0 := by simp [bitB4]


theorem source_global_galerkin_family (h41 : BITProposition41) {s : ℝ}
    (hs : 0 ≤ s) (f : Fourier) (hfr : RealValued f) (hf : InHomSobolev s f) :
    ∃ G : ℕ → ℝ → Fourier, BITGalerkinFamily s f G := by
  choose G hG hEnergy using (fun m : ℕ => h41 f hfr (hf.of_le hs) (m + 1) (by omega))
  refine ⟨G, ?_⟩
  intro m
  refine ⟨?_, hEnergy m⟩
  intro U hU
  obtain ⟨hc, hr, hODE⟩ := hG m U hU
  exact ⟨galerkin_higher_continuity hs hf hc hODE, hr, hODE⟩


/-- The differentiated old mode is c+d. Its nonzero condition survives the
cancellation producing (3.28), in addition to all nonresonant denominators. -/
theorem quartic_nonres_domain (a b c d : ℤ) :
    (a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ d ≠ 0 ∧ c + d ≠ 0 ∧
      c + d + a ≠ 0 ∧ a + b ≠ 0 ∧ b + c + d ≠ 0) ↔
    (a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ d ≠ 0 ∧ c + d ≠ 0 ∧
      (a + b) * (a + c + d) * (b + c + d) ≠ 0) := by
  rw [show c + d + a = a + c + d by ring]
  simp only [mul_ne_zero_iff]
  tauto

end BareModelCompletion
