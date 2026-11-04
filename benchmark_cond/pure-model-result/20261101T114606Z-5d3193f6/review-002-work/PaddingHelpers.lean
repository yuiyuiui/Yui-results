import ExternalBridges
noncomputable section
open scoped ENNReal
set_option maxHeartbeats 800000
namespace BareModelCompletion

/-- The amplitude used to lift a radius-R ball to the radius-2R sphere is
Lipschitz. This scalar estimate controls the *difference* of the two paddings. -/
theorem sqrt_padding_lipschitz {R x y d : ℝ} (hR : 0 < R)
    (hx : 0 ≤ x) (hxR : x ≤ R) (hy : 0 ≤ y) (hyR : y ≤ R)
    (hd : 0 ≤ d) (hxy : |x - y| ≤ d) :
    |Real.sqrt (((2 * R) ^ 2 - x ^ 2) / 2) -
      Real.sqrt (((2 * R) ^ 2 - y ^ 2) / 2)| ≤ d := by
  let a := Real.sqrt (((2 * R) ^ 2 - x ^ 2) / 2)
  let b := Real.sqrt (((2 * R) ^ 2 - y ^ 2) / 2)
  have hradx : 0 ≤ ((2 * R) ^ 2 - x ^ 2) / 2 := by nlinarith
  have hrady : 0 ≤ ((2 * R) ^ 2 - y ^ 2) / 2 := by nlinarith
  have ha : a ^ 2 = ((2 * R) ^ 2 - x ^ 2) / 2 := Real.sq_sqrt hradx
  have hb : b ^ 2 = ((2 * R) ^ 2 - y ^ 2) / 2 := Real.sq_sqrt hrady
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have haR : R ≤ a := by nlinarith
  have hbR : R ≤ b := by nlinarith
  have hsum : x + y ≤ 2 * R := by linarith
  obtain ⟨hxy1, hxy2⟩ := abs_le.mp hxy
  have upper : ∀ a b x y : ℝ,
      a ^ 2 = ((2 * R) ^ 2 - x ^ 2) / 2 →
      b ^ 2 = ((2 * R) ^ 2 - y ^ 2) / 2 →
      R ≤ a → R ≤ b → 0 ≤ x + y → x + y ≤ 2 * R → y - x ≤ d → a - b ≤ d := by
    intro a b x y ha hb haR hbR hsum0 hsum hyxd
    by_cases hab : a ≤ b
    · linarith
    have hab0 : 0 ≤ a - b := by linarith
    have hm1 := mul_nonneg (sub_nonneg.mpr hsum) hd
    have hm2 := mul_nonneg hsum0 (sub_nonneg.mpr hyxd)
    have hm3 := mul_nonneg hab0 (show 0 ≤ a + b - 2 * R by linarith)
    have hRd : 0 ≤ R * d := mul_nonneg hR.le hd
    apply (mul_le_mul_iff_right₀ hR).mp
    nlinarith
  apply abs_le.mpr
  constructor
  · have h := upper b a y x hb ha hbR haR (by linarith) (by linarith) hxy2
    linarith
  · exact upper a b x y ha hb haR hbR (by linarith) hsum (by linarith)


open KdV

/-- The weighted sequence before homogeneous reconstruction. -/
def pairedSphereLift (p : ℤ) (R : ℝ) (F : L2Seq) : L2Seq :=
  F + symmetricSpike p (Real.sqrt (((2 * R) ^ 2 - ‖F‖ ^ 2) / 2))

theorem symmetricSpike_sub (p : ℤ) (a b : ℝ) :
    symmetricSpike p a - symmetricSpike p b = symmetricSpike p (a - b) := by
  apply Subtype.ext
  funext k
  simp only [symmetricSpike, lp.coeFn_sub, lp.coeFn_add, Pi.sub_apply, Pi.add_apply,
    lp.single_apply, Pi.single_apply]
  split_ifs <;> push_cast <;> ring

theorem symmetricSpike_norm_le (p : ℤ) (a : ℝ) :
    ‖symmetricSpike p a‖ ≤ 2 * |a| := by
  calc
    _ ≤ ‖(lp.single 2 p (a : ℂ) : L2Seq)‖ + ‖(lp.single 2 (-p) (a : ℂ) : L2Seq)‖ := norm_add_le _ _
    _ = _ := by rw [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2),
      lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]; simp [Complex.norm_real, Real.norm_eq_abs]; ring

/-- A single fixed-radius sphere estimate suffices for comparison on the ball:
the simultaneous lift has a uniform bound for differences. -/
theorem pairedSphereLift_lipschitz {R : ℝ} (hR : 0 < R) (p : ℤ)
    (F G : L2Seq) (hF : ‖F‖ ≤ R) (hG : ‖G‖ ≤ R) :
    ‖pairedSphereLift p R F - pairedSphereLift p R G‖ ≤ 3 * ‖F - G‖ := by
  let a := Real.sqrt (((2 * R) ^ 2 - ‖F‖ ^ 2) / 2)
  let b := Real.sqrt (((2 * R) ^ 2 - ‖G‖ ^ 2) / 2)
  have hab : |a - b| ≤ ‖F - G‖ := sqrt_padding_lipschitz hR
    (norm_nonneg F) hF (norm_nonneg G) hG (norm_nonneg _) (abs_norm_sub_norm_le F G)
  have he : pairedSphereLift p R F - pairedSphereLift p R G =
      (F - G) + symmetricSpike p (a - b) := by
    change (F + symmetricSpike p a) - (G + symmetricSpike p b) = _
    rw [← symmetricSpike_sub p a b]
    exact add_sub_add_comm _ _ _ _
  have htri := norm_add_le (F - G) (symmetricSpike p (a - b))
  have hsp := symmetricSpike_norm_le p (a - b)
  have hsum : ‖F - G‖ + ‖symmetricSpike p (a - b)‖ ≤ ‖F - G‖ + 2 * |a - b| := by
    linarith only [hsp]
  have hfin : ‖F - G‖ + 2 * |a - b| ≤ 3 * ‖F - G‖ := by linarith only [hab]
  have hn := congrArg (fun X : L2Seq => ‖X‖) he
  exact hn.le.trans (htri.trans (hsum.trans hfin))


/-- The paired lift lies on exactly one sphere for every datum in the ball. -/
theorem pairedSphereLift_norm {R : ℝ} (hR : 0 < R) {p : ℤ} (hp : p ≠ 0)
    (F : L2Seq) (hF : ‖F‖ ≤ R) (hFp : F p = 0) (hFm : F (-p) = 0) :
    ‖pairedSphereLift p R F‖ = 2 * R := by
  have hrad : 0 ≤ ((2 * R) ^ 2 - ‖F‖ ^ 2) / 2 := by nlinarith [norm_nonneg F]
  have hs := Real.sq_sqrt hrad
  have hn := norm_add_symmetricSpike_sq hp
    (Real.sqrt (((2 * R) ^ 2 - ‖F‖ ^ 2) / 2)) F hFp hFm
  change ‖pairedSphereLift p R F‖ ^ 2 = ‖F‖ ^ 2 +
    2 * Real.sqrt (((2 * R) ^ 2 - ‖F‖ ^ 2) / 2) ^ 2 at hn
  nlinarith [norm_nonneg (pairedSphereLift p R F)]

theorem pairedSphereLift_coeff {p k : ℤ} (hkp : k ≠ p) (hkm : k ≠ -p)
    (R : ℝ) (F : L2Seq) : pairedSphereLift p R F k = F k := by
  simp [pairedSphereLift, symmetricSpike, lp.single_apply, Ne.symm hkp, Ne.symm hkm]


/-- Actual homogeneous data with the paired high-frequency lift. -/
def sourceSphereData (s R : ℝ) (m : ℕ) (f : Fourier) (hf : InHomSobolev s f) : Fourier :=
  homogeneousReconstruct s (pairedSphereLift ((m : ℤ) + 1) R
    (homogeneousLp s (cutoff m f) (hf.cutoff m)))

theorem sourceSphereData_properties {s R : ℝ} (hR : 0 < R) (m : ℕ)
    (f : Fourier) (hf : InHomSobolev s f) (hfr : RealValued f)
    (hfR : homogeneousNorm s f ≤ R) :
    RealValued (sourceSphereData s R m f hf) ∧
    InHomSobolev s (sourceSphereData s R m f hf) ∧
    homogeneousNorm s (sourceSphereData s R m f hf) = 2 * R ∧
    cutoff m (sourceSphereData s R m f hf) = cutoff m f := by
  let p : ℤ := (m : ℤ) + 1
  let F := homogeneousLp s (cutoff m f) (hf.cutoff m)
  let Q := pairedSphereLift p R F
  have hp : p ≠ 0 := by dsimp [p]; omega
  have hpo : p ∉ Finset.Icc (-(m : ℤ)) (m : ℤ) := by simp [p]
  have hmo : -p ∉ Finset.Icc (-(m : ℤ)) (m : ℤ) := by simp [p]
  have hFp : F p = 0 := by
    change homogeneousWeighted s (cutoff m f) p = 0
    rw [homogeneousWeighted_cutoff]
    simp [cutoff, hpo]
  have hFm : F (-p) = 0 := by
    change homogeneousWeighted s (cutoff m f) (-p) = 0
    rw [homogeneousWeighted_cutoff]
    simp [cutoff, hmo]
  have hF0 : F 0 = 0 := by
    change (homogeneousWeight s 0 : ℂ) * cutoff m f 0 = 0
    rw [cutoff_meanZero hf.1 m, mul_zero]
  have hQ0 : Q 0 = 0 := by
    change F 0 + symmetricSpike p _ 0 = 0
    rw [hF0, symmetricSpike_zero hp, add_zero]
  have hQr : RealValued Q.val :=
    (homogeneousWeighted_real s (cutoff_real hfr m)).add (symmetricSpike_real p _)
  have hFN : ‖F‖ ≤ R := by
    rw [homogeneousLp_norm]
    exact (homogeneousNorm_cutoff_le hf m).trans hfR
  refine ⟨homogeneousReconstruct_real s Q hQr,
    homogeneousReconstruct_inHomSobolev s Q hQ0, ?_, ?_⟩
  · change homogeneousNorm s (homogeneousReconstruct s Q) = _
    rw [homogeneousReconstruct_norm s Q hQ0]
    exact pairedSphereLift_norm hR hp F hFN hFp hFm
  · funext k
    by_cases hki : k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ)
    · simp only [cutoff, if_pos hki]
      by_cases hk : k = 0
      · subst k
        have hf0 : f 0 = 0 := hf.1
        simp [sourceSphereData, homogeneousReconstruct, hf0]
      · have hkp : k ≠ p := by intro he; subst k; exact hpo hki
        have hkm : k ≠ -p := by intro he; subst k; exact hmo hki
        have hQk : Q k = (homogeneousWeight s k : ℂ) * f k := by
          rw [pairedSphereLift_coeff hkp hkm]
          change (homogeneousWeight s k : ℂ) * cutoff m f k = _
          simp [cutoff, hki]
        change (if k = 0 then 0 else (homogeneousWeight s k : ℂ)⁻¹ * Q k) = f k
        rw [if_neg hk, hQk, ← mul_assoc,
          inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (homogeneousWeight_pos_of_ne_zero s hk).ne'), one_mul]
    · simp [cutoff, hki]


theorem homogeneousReconstruct_sub (s : ℝ) (F G : L2Seq) :
    homogeneousReconstruct s (F - G) = homogeneousReconstruct s F - homogeneousReconstruct s G := by
  funext k
  by_cases hk : k = 0 <;> simp [homogeneousReconstruct, hk, mul_sub]

theorem sourceSphereData_difference {s R : ℝ} (hR : 0 < R) (m : ℕ)
    (f g : Fourier) (hf : InHomSobolev s f) (hg : InHomSobolev s g)
    (hfR : homogeneousNorm s f ≤ R) (hgR : homogeneousNorm s g ≤ R) :
    homogeneousNorm s (sourceSphereData s R m f hf - sourceSphereData s R m g hg) ≤
      3 * homogeneousNorm s (f - g) := by
  let p : ℤ := (m : ℤ) + 1
  let F := homogeneousLp s (cutoff m f) (hf.cutoff m)
  let G := homogeneousLp s (cutoff m g) (hg.cutoff m)
  let QF := pairedSphereLift p R F
  let QG := pairedSphereLift p R G
  have hp : p ≠ 0 := by dsimp [p]; omega
  have hQ0 (H : L2Seq) (hH : H 0 = 0) : pairedSphereLift p R H 0 = 0 := by
    change H 0 + symmetricSpike p _ 0 = 0
    rw [hH, symmetricSpike_zero hp, add_zero]
  have hF0 : F 0 = 0 := by
    change (homogeneousWeight s 0 : ℂ) * cutoff m f 0 = 0
    rw [cutoff_meanZero hf.1, mul_zero]
  have hG0 : G 0 = 0 := by
    change (homogeneousWeight s 0 : ℂ) * cutoff m g 0 = 0
    rw [cutoff_meanZero hg.1, mul_zero]
  have hD0 : (QF - QG) 0 = 0 := by
    change QF 0 - QG 0 = 0
    rw [hQ0 F hF0, hQ0 G hG0, sub_self]
  have hFN : ‖F‖ ≤ R := by
    rw [homogeneousLp_norm]
    exact (homogeneousNorm_cutoff_le hf m).trans hfR
  have hGN : ‖G‖ ≤ R := by
    rw [homogeneousLp_norm]
    exact (homogeneousNorm_cutoff_le hg m).trans hgR
  have hDiff : F - G = homogeneousLp s (cutoff m (f - g)) ((hf.sub hg).cutoff m) := by
    apply Subtype.ext
    change homogeneousWeighted s (cutoff m f) - homogeneousWeighted s (cutoff m g) = _
    rw [← homogeneousWeighted_sub, ← cutoff_sub]
    rfl
  have hNormDiff : ‖F - G‖ ≤ homogeneousNorm s (f - g) := by
    rw [hDiff, homogeneousLp_norm]
    exact homogeneousNorm_cutoff_le (hf.sub hg) m
  change homogeneousNorm s (homogeneousReconstruct s QF - homogeneousReconstruct s QG) ≤ _
  rw [← homogeneousReconstruct_sub, homogeneousReconstruct_norm s (QF - QG) hD0]
  have hb := pairedSphereLift_lipschitz hR p F G hFN hGN
  exact hb.trans (by linarith only [hNormDiff])


theorem negative_weight_tendsto_zero {s : ℝ} (hs : 0 < s) :
    Filter.Tendsto (fun n : ℕ => weight (-s) (n : ℤ)) Filter.atTop (nhds 0) := by
  have hb : Filter.Tendsto (fun n : ℕ => 1 + (n : ℝ) ^ 2) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_mono (f := fun n : ℕ => (n : ℝ))
    · intro n
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      nlinarith [sq_nonneg ((n : ℝ) - 1 / 2)]
    · exact tendsto_natCast_atTop_atTop
  have hw := (tendsto_rpow_neg_atTop (show 0 < s / 2 by linarith)).comp hb
  simpa [weight, neg_div, Function.comp_def] using hw

/-- Padding at frequencies escaping to infinity disappears in L2 for every
strictly positive Sobolev exponent, even though its H^s size stays fixed. -/
theorem sourceSphereData_L2_converges {s R : ℝ} (hs : 0 < s) (hR : 0 < R)
    (f : Fourier) (hf : InHomSobolev s f) (hfr : RealValued f)
    (hfR : homogeneousNorm s f ≤ R) :
    Filter.Tendsto (fun n : ℕ => homogeneousNorm 0 (sourceSphereData s R n f hf - f))
      Filter.atTop (nhds 0) := by
  let D : ℕ → Fourier := fun n => sourceSphereData s R n f hf - f
  let C : ℝ := (2 : ℝ) ^ s * (3 * R)
  have hb (n : ℕ) : hNorm 0 (D n) ≤ weight (-s) (n : ℤ) * C := by
    obtain ⟨_, hpad, hnorm, hlow⟩ := sourceSphereData_properties hR n f hf hfr hfR
    have hD : InHomSobolev s (D n) := hpad.sub hf
    have hcut : cutoff n (D n) = 0 := by
      change cutoff n (sourceSphereData s R n f hf - f) = 0
      rw [cutoff_sub, hlow, sub_self]
    have hhigh : highCutoff n (D n) = D n := by simp [highCutoff, hcut]
    have hHs : hNorm s (D n) ≤ C := by
      have hd := homogeneousNorm_sub_le hpad hf
      change homogeneousNorm s (D n) ≤ _ at hd
      have hbd : homogeneousNorm s (D n) ≤ 3 * R := by rw [hnorm] at hd; linarith
      exact (hNorm_le_homogeneousNorm hs.le hD).trans
        (mul_le_mul_of_nonneg_left hbd (Real.rpow_nonneg (by norm_num) _))
    have hh := (high_cutoff_bound hs.le (hD.to_inhomogeneous hs.le) n).2
    rw [hhigh] at hh
    simp only [zero_sub] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hHs (weight_pos _ _).le)
  have hw := (negative_weight_tendsto_zero hs).mul_const C
  have he := squeeze_zero (fun n => hNorm_nonneg 0 (D n)) hb (by simpa using hw)
  simpa only [homogeneousNorm_zero] using he

end BareModelCompletion
