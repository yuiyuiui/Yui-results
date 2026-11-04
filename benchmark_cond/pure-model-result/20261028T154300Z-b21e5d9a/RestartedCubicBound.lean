import AffineInputRepresentation
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV
set_option maxHeartbeats 800000

def errorCubicInputs (externalStep : LiWuStepIdentity) {T τ : ℝ}
    (hT : 0 ≤ T) (hτ : 0 < τ) (f : Sobolev 2) (hfr : RealValued f.val) (hfm : MeanZero f.val)
    {u : ℝ → Fourier} (hu : KdVSolution 2 T f.val u) (k : ℕ)
    (i : Fin 3) (z : Fin 3 → ℂ) (j : Fin 3) (t : ℝ) : Sobolev 1 :=
  if j = i then errorPath externalStep hT hτ f hfr hfm hu k t
  else affineErrorPath externalStep hT hτ f hfr hfm hu k (z j) t

/-- The two cubic terms in (31) are covered by choosing the error slot and
 the affine coefficients. The small error factor remains explicit. -/
theorem restarted_cubic_bound (externalStep : LiWuStepIdentity)
    (externalStage : LiWuStageEstimate) (externalProduct : LiWuProductEstimate)
    (externalTrilinear : LiWuTrilinearEstimate)
    {T γ M : ℝ} (hT : 0 < T) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, ∀ hτ : 0 < τ, τ ≤ 1 → ∀ k : ℕ,
      ((k + 1 : ℕ) : ℝ) * τ ≤ T →
      ∀ f : Sobolev 2, ∀ hfr : RealValued f.val, ∀ hfm : MeanZero f.val,
      ∀ u : ℝ → Fourier, ∀ hu : KdVSolution 2 T f.val u,
        (∀ t ∈ Set.Icc 0 T, hNorm γ (u t) ≤ M) →
        ∀ j0 : ℕ, j0 ≤ k → ∀ b E : ℝ, (j0 : ℝ) * τ ≤ b → b ≤ ((k + 1 : ℕ) : ℝ) * τ →
          b - (j0 : ℝ) * τ ≤ 1 → 0 ≤ E → E ≤ 1 →
          (∀ t ∈ Set.Icc ((j0 : ℝ) * τ) b,
            hNorm 0 (errorPath externalStep hT.le hτ f hfr hfm hu k t).val ≤ E) →
          ∀ m : ℕ, ∀ i : Fin 3, ∀ z : Fin 3 → ℂ, (∀ j, ‖z j‖ ≤ 1) →
          let F := errorCubicInputs externalStep hT.le hτ f hfr hfm hu k i z
          InSobolev 0 (highCutoff (3 * m) (pathCubic ((j0 : ℝ) * τ) b F)) ∧
          hNorm 0 (highCutoff (3 * m) (pathCubic ((j0 : ℝ) * τ) b F)) ≤
            C * ((b - (j0 : ℝ) * τ) * τ ^ γ +
              (b - (j0 : ℝ) * τ + weight (-pStar) (m : ℤ)) * E) := by
  obtain ⟨Ce, hCe, hError⟩ := restarted_error_time_bound externalStep externalStage externalProduct externalTrilinear hT hγ hγ1 hM
  obtain ⟨Ca, hCa, hAffine⟩ := restarted_affine_error_time_bounds externalStep externalStage externalProduct externalTrilinear hT hγ hγ1 hM
  obtain ⟨Cp, hCp, hHigh⟩ := high_output_small_bound externalTrilinear
  refine ⟨Cp * (Ce + 1) * Ca ^ 2, by positivity, ?_⟩
  intro τ hτ hτ1 k hTotal f hfr hfm u hu huM j0 hj0 b E hab hb hlen hE hE1 he m i z hz
  dsimp only
  let a : ℝ := (j0 : ℝ) * τ
  let q := τ ^ γ + E
  let F := errorCubicInputs externalStep hT.le hτ f hfr hfm hu k i z
  let D : Fin 3 → ℝ → Sobolev (-pStar) := fun j => if j = i then
    errorNegativeDerivative externalStep hT.le hτ f hfr hfm hu k else
    affineNegativeDerivative externalStep hT.le hτ f hfr hfm hu k (z j)
  have ha : 0 ≤ a := mul_nonneg (Nat.cast_nonneg _) hτ.le
  obtain ⟨he0, hde, hwe⟩ := error_time_membership externalStep hT.le hτ k hTotal f hfr hfm hu ha hab hb
  have hxa := hError τ hτ hτ1 k hTotal f hfr hfm u hu huM j0 hj0 b E hab hb hE hE1 he
  have haff (j : Fin 3) := affine_input_time_membership externalStep hT.le hτ k hTotal f hfr hfm hu (z j) ha hab hb
  have hFC (j : Fin 3) : Continuous (F j) := by
    change Continuous (fun t => if j = i then errorPath externalStep hT.le hτ f hfr hfm hu k t
      else affineErrorPath externalStep hT.le hτ f hfr hfm hu k (z j) t)
    by_cases hj : j = i
    · simp only [if_pos hj]
      exact continuous_errorPath externalStep hT.le hτ f hfr hfm hu k
    · simp only [if_neg hj]
      exact continuous_affineErrorPath externalStep hT.le hτ f hfr hfm hu k (z j)
  have hDm (j : Fin 3) : MemLp (D j) ∞ (volume.restrict (Set.Icc a b)) := by
    dsimp [D]
    split_ifs
    · exact hde
    · exact (haff j).2.1
  have hW (j : Fin 3) : WeakTimeDerivative a b (fun t => (F j t).val) (fun t => (D j t).val) := by
    by_cases hj : j = i
    · simpa only [F, D, errorCubicInputs, hj, if_pos rfl, ↓reduceIte, errorL2Path, inclusionMap_val] using hwe
    · simpa only [F, D, errorCubicInputs, if_neg hj, affineL2Path, inclusionMap_val] using (haff j).2.2
  have hXi : timeXNorm a b (fun t => inclusionMap 0 1 (by norm_num) (F i t)) (D i) ≤ Ce * q := by
    simp only [F, D, errorCubicInputs, if_pos rfl, ite_true]
    exact hxa
  have hLi : timeLInfinity a b (fun t => inclusionMap 0 1 (by norm_num) (F i t)) ≤ E := by
    apply timeLInfinity_le_of_bound hE
    intro t ht
    rw [sobolev_norm]
    simpa only [F, errorCubicInputs, if_pos rfl, ite_true, inclusionMap_val] using he t ht
  have hX (j : Fin 3) (hj : j ≠ i) : timeXNorm a b (fun t => inclusionMap 0 1 (by norm_num) (F j t)) (D j) ≤ Ca := by
    simp only [F, D, errorCubicInputs, if_neg hj]
    change timeXNorm a b (affineL2Path externalStep hT.le hτ f hfr hfm hu k (z j))
      (affineNegativeDerivative externalStep hT.le hτ f hfr hfm hu k (z j)) ≤ Ca
    rw [affineL2Path_eq]
    exact hAffine τ hτ hτ1 k hTotal f hfr hfm u hu huM j0 hj0 b E hab hb hE hE1 he (z j) (hz j)
  obtain ⟨hmem, hn⟩ := hHigh a b ha hab hlen F hFC D hDm hW m i (Ce * q) E Ca hXi hLi hX
  refine ⟨hmem, hn.trans ?_⟩
  have hlen0 : 0 ≤ b - a := sub_nonneg.mpr hab
  have hτγ : 0 ≤ τ ^ γ := Real.rpow_nonneg hτ.le γ
  have hweight := (weight_pos (-pStar) (m : ℤ)).le
  dsimp [q]
  apply sub_nonneg.mp
  calc
    _ = Cp * Ca ^ 2 * ((b - a) * τ ^ γ + (b - a) * E + Ce * weight (-pStar) (m : ℤ) * E) := by ring
    _ ≥ 0 := by positivity

end KdV
