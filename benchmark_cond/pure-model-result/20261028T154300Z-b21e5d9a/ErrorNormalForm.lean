import Proof
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

theorem sobolev_val_sub {s : ℝ} (f g : Sobolev s) : (f - g).val = f.val - g.val := rfl

theorem sobolev_val_smul {s : ℝ} (z : ℂ) (f : Sobolev s) : (z • f).val = z • f.val := rfl

/-- Equation (31) on a restarted interval. The exact and perturbed equations
are explicit internal hypotheses; their algebra is proved here, and the
normal-form integration handles derivative jumps at the numerical grid. -/
theorem error_normal_form_grid (τ : ℝ) (hτ : 0 < τ) (k : ℕ)
    (v V : ℝ → Sobolev 1) (dv dV : ℕ → ℝ → Sobolev 1) (r : ℕ → ℝ → Sobolev 0)
    (hv : Continuous v) (hV : Continuous V)
    (hdv : ∀ j, Continuous (dv j)) (hdV : ∀ j, Continuous (dV j)) (hr : ∀ j, Continuous (r j))
    (hvd : ∀ j ≤ k, ∀ t ∈ Set.Ioo ((j : ℝ) * τ) (((j + 1 : ℕ) : ℝ) * τ), ∀ m : ℤ,
      HasDerivAt (fun s : ℝ => (v s).val m) ((dv j t).val m) t)
    (hVd : ∀ j ≤ k, ∀ t ∈ Set.Ioo ((j : ℝ) * τ) (((j + 1 : ℕ) : ℝ) * τ), ∀ m : ℤ,
      HasDerivAt (fun s : ℝ => (V s).val m) ((dV j t).val m) t)
    (hvEq : ∀ j ≤ k, ∀ t ∈ Set.Icc ((j : ℝ) * τ) (((j + 1 : ℕ) : ℝ) * τ),
      (dv j t).val = (1 / 2 : ℂ) • B t (v t).val (v t).val)
    (hVEq : ∀ j ≤ k, ∀ t ∈ Set.Icc ((j : ℝ) * τ) (((j + 1 : ℕ) : ℝ) * τ),
      (dV j t).val = (1 / 2 : ℂ) • B t (V t).val (V t).val + (r j t).val)
    (hvm : ∀ t, MeanZero (v t).val) (hVm : ∀ t, MeanZero (V t).val)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ ((k + 1 : ℕ) : ℝ) * τ) (m : ℤ) :
    let e : ℝ → Sobolev 1 := fun t => v t - V t
    let g : ℝ → Sobolev 1 := fun t => v t - (1 / 2 : ℂ) • e t
    (∫ t : ℝ in a..b, B t (e t).val (g t).val m) =
      (1 / 3 : ℂ) * (J b (e b).val (g b).val m - J a (e a).val (g a).val m) -
      (1 / 3 : ℂ) * CIntegral a b (fun t => (e t).val) (fun t => (g t).val) (fun t => (V t).val) m -
      (1 / 6 : ℂ) * CIntegral a b (fun t => (v t).val) (fun t => (v t).val) (fun t => (e t).val) m +
      (1 / 3 : ℂ) * ∫ t : ℝ in a..b, J t (concatenate τ r k t).val (V t).val m := by
  dsimp only
  let e : ℝ → Sobolev 1 := fun t => v t - V t
  let g : ℝ → Sobolev 1 := fun t => v t - (1 / 2 : ℂ) • e t
  let de : ℕ → ℝ → Sobolev 1 := fun j t => dv j t - dV j t
  let dg : ℕ → ℝ → Sobolev 1 := fun j t => dv j t - (1 / 2 : ℂ) • de j t
  have heC : Continuous e := hv.sub hV
  have hgC : Continuous g := hv.sub ((continuous_const (y := (1 / 2 : ℂ))).smul heC)
  have hdeC (j : ℕ) : Continuous (de j) := (hdv j).sub (hdV j)
  have hdgC (j : ℕ) : Continuous (dg j) := (hdv j).sub ((continuous_const (y := (1 / 2 : ℂ))).smul (hdeC j))
  have hed : ∀ j ≤ k, ∀ t ∈ Set.Ioo ((j : ℝ) * τ) (((j + 1 : ℕ) : ℝ) * τ), ∀ l : ℤ,
      HasDerivAt (fun s : ℝ => (e s).val l) ((de j t).val l) t := by
    intro j hj t ht l
    exact (hvd j hj t ht l).sub (hVd j hj t ht l)
  have hgd : ∀ j ≤ k, ∀ t ∈ Set.Ioo ((j : ℝ) * τ) (((j + 1 : ℕ) : ℝ) * τ), ∀ l : ℤ,
      HasDerivAt (fun s : ℝ => (g s).val l) ((dg j t).val l) t := by
    intro j hj t ht l
    exact (hvd j hj t ht l).sub ((hed j hj t ht l).const_mul (1 / 2 : ℂ))
  have hem (t : ℝ) : MeanZero (e t).val := (hvm t).sub (hVm t)
  have hgm (t : ℝ) : MeanZero (g t).val := (hvm t).sub ((hem t).smul (1 / 2 : ℂ))
  have hNF := variable_normal_form_grid τ hτ k e g de dg heC hgC hdeC hdgC hed hgd hem hgm ha hab hb m
  have hpoint (t : ℝ) (ht : t ∈ Set.Ioo a b) (hnot : t ∉ Set.range (fun j : ℕ => (j : ℝ) * τ)) :
      J t (concatenate τ de k t).val (g t).val m + J t (e t).val (concatenate τ dg k t).val m =
        CIntegrand t (e t).val (g t).val (V t).val m +
        (1 / 2 : ℂ) * CIntegrand t (v t).val (v t).val (e t).val m -
        J t (concatenate τ r k t).val (V t).val m := by
    have hnot' : ∀ j : ℕ, t ≠ (j : ℝ) * τ := fun j heq => hnot ⟨j, heq.symm⟩
    obtain ⟨j, hj, hstep⟩ := exists_open_grid_step hτ k
      (lt_of_le_of_lt ha ht.1) (lt_of_lt_of_le ht.2 hb) hnot'
    have hstepc : t ∈ Set.Icc ((j : ℝ) * τ) (((j + 1 : ℕ) : ℝ) * τ) := ⟨hstep.1.le, hstep.2.le⟩
    have hdeEq : (de j t).val = B t (e t).val (g t).val - (r j t).val := by
      change (dv j t).val - (dV j t).val = _
      rw [hvEq j hj t hstepc, hVEq j hj t hstepc]
      change (1 / 2 : ℂ) • B t (v t).val (v t).val -
        ((1 / 2 : ℂ) • B t (V t).val (V t).val + (r j t).val) =
        B t ((v t).val - (V t).val) ((v t).val - (1 / 2 : ℂ) • ((v t).val - (V t).val)) - (r j t).val
      rw [B_error_polarization ((v t).property.of_le (by norm_num)) ((V t).property.of_le (by norm_num))]
      module
    have hdgEq : (dg j t).val = (1 / 2 : ℂ) • B t (v t).val (v t).val -
        (1 / 2 : ℂ) • B t (e t).val (g t).val + (1 / 2 : ℂ) • (r j t).val := by
      change (dv j t).val - (1 / 2 : ℂ) • (de j t).val = _
      rw [hvEq j hj t hstepc, hdeEq]
      module
    rw [concatenate_on_open_step hτ.le de hj hstep, concatenate_on_open_step hτ.le dg hj hstep,
      concatenate_on_open_step hτ.le r hj hstep, hdeEq, hdgEq]
    simpa only [e, g, sobolev_val_sub, sobolev_val_smul,
      Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using
      congrFun (error_normal_form_integrand t (v t) (V t) (r j t)) m
  have hIntEq : (∫ t : ℝ in a..b,
      (J t (concatenate τ de k t).val (g t).val m + J t (e t).val (concatenate τ dg k t).val m)) =
      ∫ t : ℝ in a..b, (CIntegrand t (e t).val (g t).val (V t).val m +
        (1 / 2 : ℂ) * CIntegrand t (v t).val (v t).val (e t).val m -
        J t (concatenate τ r k t).val (V t).val m) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [(Set.countable_range (fun j : ℕ => (j : ℝ) * τ)).ae_notMem volume, volume.ae_ne b]
      with t hnot htb
    intro ht
    rw [Set.uIoc_of_le hab] at ht
    exact hpoint t ⟨ht.1, lt_of_le_of_ne ht.2 htb⟩ hnot
  have hiC : IntervalIntegrable (fun t : ℝ => CIntegrand t (e t).val (g t).val (V t).val m) volume a b :=
    (continuous_CIntegrand_paths heC hgC hV m).intervalIntegrable a b
  have hiC2 : IntervalIntegrable (fun t : ℝ => CIntegrand t (v t).val (v t).val (e t).val m) volume a b :=
    (continuous_CIntegrand_paths hv hv heC m).intervalIntegrable a b
  have hiR : IntervalIntegrable (fun t : ℝ => J t (concatenate τ r k t).val (V t).val m) volume a b := by
    have hc (j : ℕ) : Continuous (fun t : ℝ => J t (r j t).val (V t).val m) := by
      have h := (coefficientMap 1 m).continuous.comp (continuous_JZeroBundled continuous_id (hr j)
        ((inclusionMap 0 1 (by norm_num)).continuous.comp hV))
      simp only [Function.comp_def, coefficientMap_apply, JZeroBundled_val, inclusionMap_val, id_eq] at h
      exact h
    have hi := intervalIntegrable_concatenate τ (fun j t => J t (r j t).val (V t).val m)
      (fun j => (hc j).intervalIntegrable a b) k
    have hmap : concatenate τ (fun j t => J t (r j t).val (V t).val m) k =
        (fun t => J t (concatenate τ r k t).val (V t).val m) := by
      funext t
      exact concatenate_map τ r (fun s w => J s w.val (V s).val m) k t
    rwa [hmap] at hi
  rw [hIntEq, intervalIntegral.integral_sub (hiC.add (hiC2.const_mul _)) hiR,
    intervalIntegral.integral_add hiC (hiC2.const_mul _), intervalIntegral.integral_const_mul] at hNF
  change (∫ t : ℝ in a..b, B t (e t).val (g t).val m) =
    (1 / 3 : ℂ) * (J b (e b).val (g b).val m - J a (e a).val (g a).val m) -
    (1 / 3 : ℂ) * (∫ t : ℝ in a..b, CIntegrand t (e t).val (g t).val (V t).val m) -
    (1 / 6 : ℂ) * (∫ t : ℝ in a..b, CIntegrand t (v t).val (v t).val (e t).val m) +
    (1 / 3 : ℂ) * (∫ t : ℝ in a..b, J t (concatenate τ r k t).val (V t).val m)
  linear_combination hNF

end KdV
