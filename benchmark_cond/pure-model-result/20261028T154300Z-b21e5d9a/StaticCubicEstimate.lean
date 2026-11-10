import Proof
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

theorem CIntegral_static_sub_left {f l g h : Fourier}
    (hf : InSobolev 0 f) (hl : InSobolev 0 l) (hg : InSobolev 0 g) (hh : InSobolev 0 h) (a b : ℝ) :
    CIntegral a b (fun _ => f - l) (fun _ => g) (fun _ => h) =
      CIntegral a b (fun _ => f) (fun _ => g) (fun _ => h) -
        CIntegral a b (fun _ => l) (fun _ => g) (fun _ => h) := by
  have ha := CIntegral_static_add_left (hf.sub hl) hl hg hh a b
  simp only [sub_add_cancel] at ha
  exact eq_sub_iff_add_eq.mpr ha.symm

theorem CIntegral_static_sub_middle {f g l h : Fourier}
    (hf : InSobolev 0 f) (hg : InSobolev 0 g) (hl : InSobolev 0 l) (hh : InSobolev 0 h) (a b : ℝ) :
    CIntegral a b (fun _ => f) (fun _ => g - l) (fun _ => h) =
      CIntegral a b (fun _ => f) (fun _ => g) (fun _ => h) -
        CIntegral a b (fun _ => f) (fun _ => l) (fun _ => h) := by
  have ha := CIntegral_static_add_middle hf (hg.sub hl) hl hh a b
  simp only [sub_add_cancel] at ha
  exact eq_sub_iff_add_eq.mpr ha.symm

theorem CIntegral_static_sub_right {f g h l : Fourier}
    (hf : InSobolev 0 f) (hg : InSobolev 0 g) (hh : InSobolev 0 h) (hl : InSobolev 0 l) (a b : ℝ) :
    CIntegral a b (fun _ => f) (fun _ => g) (fun _ => h - l) =
      CIntegral a b (fun _ => f) (fun _ => g) (fun _ => h) -
        CIntegral a b (fun _ => f) (fun _ => g) (fun _ => l) := by
  have ha := CIntegral_static_add_right hf hg (hh.sub hl) hl a b
  simp only [sub_add_cancel] at ha
  exact eq_sub_iff_add_eq.mpr ha.symm

theorem CIntegral_static_diagonal_sub {f w : Fourier}
    (hf : InSobolev 0 f) (hw : InSobolev 0 w) (a b : ℝ) :
    CIntegral a b (fun _ => f) (fun _ => f) (fun _ => f) -
      CIntegral a b (fun _ => w) (fun _ => w) (fun _ => w) =
      CIntegral a b (fun _ => f - w) (fun _ => f) (fun _ => f) +
      CIntegral a b (fun _ => w) (fun _ => f - w) (fun _ => f) +
      CIntegral a b (fun _ => w) (fun _ => w) (fun _ => f - w) := by
  rw [CIntegral_static_sub_left hf hw hf hf,
    CIntegral_static_sub_middle hw hf hw hf, CIntegral_static_sub_right hw hw hf hw]
  abel

/-- The static trilinear term at a numerical state is controlled by the exact
state's Sobolev norm and their `L²` distance, by three internal telescoping terms. -/
theorem numerical_static_cubic_bound (externalTrilinear : LiWuTrilinearEstimate)
    {γ M : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
      ∀ a b : ℝ, 0 ≤ a → a ≤ b → b - a ≤ τ →
      ∀ f w : Fourier, InSobolev 0 f → InSobolev γ w →
        hNorm γ w ≤ M → hNorm 0 (f - w) ≤ 1 →
        InSobolev 0 (CIntegral a b (fun _ => f) (fun _ => f) (fun _ => f)) ∧
        hNorm 0 (CIntegral a b (fun _ => f) (fun _ => f) (fun _ => f)) ≤
          C * (τ ^ γ + hNorm 0 (f - w)) := by
  obtain ⟨Cγ, hCγ, hbγ⟩ := normalized_static_trilinear externalTrilinear
    (by norm_num : (0 : ℝ) < 1) hγ.le hγ1
  obtain ⟨C0, hC0, hb0⟩ := normalized_static_trilinear externalTrilinear
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 1)
  let A : ℝ := Cγ * M ^ 3
  let D : ℝ := 3 * C0 * (M + 1) ^ 2
  have hA : 0 ≤ A := mul_nonneg hCγ.le (by positivity)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨1 + A + D, by linarith, ?_⟩
  intro τ hτ hτ1 a b ha hab hb f w hf hw hwM hδ
  have hwγ0 := hNorm_nonneg γ w
  have hw00 := hNorm_nonneg 0 w
  have hf00 := hNorm_nonneg 0 f
  have hd00 := hNorm_nonneg 0 (f - w)
  have hb1 : b - a ≤ 1 := hb.trans hτ1
  have hw0 := hw.of_le hγ.le
  have hd := hf.sub hw0
  have hwM0 : hNorm 0 w ≤ M := (hNorm_mono hw hγ.le).trans hwM
  have hfM0 : hNorm 0 f ≤ M + 1 := by
    have hh := hNorm_add_le hd hw0
    rw [sub_add_cancel] at hh
    linarith
  obtain ⟨hww, hwwb⟩ := hbγ a b ha hab hb1 w w w hw hw hw
  have hwwb' : hNorm 0 (CIntegral a b (fun _ => w) (fun _ => w) (fun _ => w)) ≤ A * τ ^ γ := by
    calc
      _ ≤ Cγ * (b - a) ^ γ * hNorm γ w * hNorm γ w * hNorm γ w := hwwb
      _ ≤ Cγ * τ ^ γ * M * M * M := by
        gcongr
      _ = _ := by dsimp [A]; ring
  obtain ⟨h1, hb1'⟩ := hb0 a b ha hab hb1 (f - w) f f hd hf hf
  obtain ⟨h2, hb2'⟩ := hb0 a b ha hab hb1 w (f - w) f hw0 hd hf
  obtain ⟨h3, hb3'⟩ := hb0 a b ha hab hb1 w w (f - w) hw0 hw0 hd
  simp only [Real.rpow_zero, mul_one] at hb1' hb2' hb3'
  have h1b : hNorm 0 (CIntegral a b (fun _ => f - w) (fun _ => f) (fun _ => f)) ≤
      C0 * (M + 1) ^ 2 * hNorm 0 (f - w) := by
    calc
      _ ≤ C0 * hNorm 0 (f - w) * hNorm 0 f * hNorm 0 f := hb1'
      _ ≤ C0 * hNorm 0 (f - w) * (M + 1) * (M + 1) := by gcongr
      _ = _ := by ring
  have h2b : hNorm 0 (CIntegral a b (fun _ => w) (fun _ => f - w) (fun _ => f)) ≤
      C0 * (M + 1) ^ 2 * hNorm 0 (f - w) := by
    calc
      _ ≤ C0 * hNorm 0 w * hNorm 0 (f - w) * hNorm 0 f := hb2'
      _ ≤ C0 * (M + 1) * hNorm 0 (f - w) * (M + 1) := by gcongr; linarith
      _ = _ := by ring
  have h3b : hNorm 0 (CIntegral a b (fun _ => w) (fun _ => w) (fun _ => f - w)) ≤
      C0 * (M + 1) ^ 2 * hNorm 0 (f - w) := by
    calc
      _ ≤ C0 * hNorm 0 w * hNorm 0 w * hNorm 0 (f - w) := hb3'
      _ ≤ C0 * (M + 1) * (M + 1) * hNorm 0 (f - w) := by gcongr <;> linarith
      _ = _ := by ring
  have hEq : CIntegral a b (fun _ => f) (fun _ => f) (fun _ => f) =
      CIntegral a b (fun _ => w) (fun _ => w) (fun _ => w) +
        ((CIntegral a b (fun _ => f - w) (fun _ => f) (fun _ => f) +
          CIntegral a b (fun _ => w) (fun _ => f - w) (fun _ => f)) +
          CIntegral a b (fun _ => w) (fun _ => w) (fun _ => f - w)) := by
    have hh := CIntegral_static_diagonal_sub hf hw0 a b
    linear_combination hh
  rw [hEq]
  refine ⟨hww.add ((h1.add h2).add h3), ?_⟩
  have hsum := hNorm_add_le hww ((h1.add h2).add h3)
  have hsum' := hNorm_add_le (h1.add h2) h3
  have hsum'' := hNorm_add_le h1 h2
  have hq0 := Real.rpow_nonneg hτ.le γ
  have hd0 := hNorm_nonneg 0 (f - w)
  dsimp [D]
  nlinarith

end KdV
