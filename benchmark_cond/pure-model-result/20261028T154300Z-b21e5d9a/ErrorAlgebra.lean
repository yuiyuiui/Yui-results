import Proof
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV

theorem J_add_left {f g h : Fourier} (hf : InSobolev 0 f) (hg : InSobolev 0 g)
    (hh : InSobolev 0 h) (t : ℝ) : J t (f + g) h = J t f h + J t g h := by
  have heq := J_sub_left (hf.add hg) hg hh t
  rw [add_sub_cancel_right] at heq
  exact (eq_sub_iff_add_eq.mp heq).symm

theorem J_add_right {f g h : Fourier} (hf : InSobolev 0 f) (hg : InSobolev 0 g)
    (hh : InSobolev 0 h) (t : ℝ) : J t f (g + h) = J t f g + J t f h := by
  rw [J_comm t f (g + h), J_add_left hg hh hf, J_comm t g f, J_comm t h f]

theorem B_error_polarization {v V : Fourier} (hv : InSobolev 0 v) (hV : InSobolev 0 V) (t : ℝ) :
    B t (v - V) (v - (1 / 2 : ℂ) • (v - V)) = (1 / 2 : ℂ) • (B t v v - B t V V) := by
  have hg : v - (1 / 2 : ℂ) • (v - V) = (1 / 2 : ℂ) • (v + V) := by module
  rw [hg, B_smul_right, B_sub_left hv hV (hv.add hV), B_add_right hv hv hV,
    B_add_right hV hv hV, B_comm t V v]
  module

/-- The differentiated algebra in (31), before time integration. It is proved
for actual `H¹` states and an arbitrary `L²` residual derivative. -/
theorem error_normal_form_integrand (t : ℝ) (v V : Sobolev 1) (r : Sobolev 0) :
    let e := v.val - V.val
    let g := v.val - (1 / 2 : ℂ) • e
    let de := B t e g - r.val
    let dg := (1 / 2 : ℂ) • B t v.val v.val - (1 / 2 : ℂ) • B t e g + (1 / 2 : ℂ) • r.val
    J t de g + J t e dg = CIntegrand t e g V.val +
      (1 / 2 : ℂ) • CIntegrand t v.val v.val e - J t r.val V.val := by
  dsimp only
  let e := v.val - V.val
  let g := v.val - (1 / 2 : ℂ) • e
  have he1 : InSobolev 1 e := v.property.sub V.property
  have hg1 : InSobolev 1 g := v.property.sub (he1.smul (1 / 2 : ℂ))
  have he := he1.of_le (by norm_num : (0 : ℝ) ≤ 1)
  have hg := hg1.of_le (by norm_num : (0 : ℝ) ≤ 1)
  have hv := v.property.of_le (by norm_num : (0 : ℝ) ≤ 1)
  have hB := (B_h1_bound he1 hg1 t).1
  have hBv := (B_h1_bound v.property v.property t).1
  change J t (B t e g - r.val) g + J t e
      ((1 / 2 : ℂ) • B t v.val v.val - (1 / 2 : ℂ) • B t e g + (1 / 2 : ℂ) • r.val) = _
  rw [J_sub_left hB r.property hg, J_add_right he
      ((hBv.smul (1 / 2 : ℂ)).sub (hB.smul (1 / 2 : ℂ))) (r.property.smul (1 / 2 : ℂ)),
    J_sub_right he (hBv.smul (1 / 2 : ℂ)) (hB.smul (1 / 2 : ℂ)),
    J_smul_right, J_smul_right, J_smul_right,
    J_comm t e (B t v.val v.val), J_comm t e (B t e g), J_comm t e r.val]
  rw [J_B, J_B, J_B]
  have hV : V.val = g - (1 / 2 : ℂ) • e := by dsimp [g, e]; module
  have hc : CIntegrand t e g V.val = CIntegrand t e g g - (1 / 2 : ℂ) • CIntegrand t e g e := by
    have hh := CIntegrand_add_right he hg (V.property.of_le (by norm_num : (0 : ℝ) ≤ 1))
      (he.smul (1 / 2 : ℂ)) t
    have hsum : V.val + (1 / 2 : ℂ) • e = g := by dsimp [g, e]; module
    rw [hsum, CIntegrand_smul_right] at hh
    exact eq_sub_iff_add_eq.mpr hh.symm
  have hj : J t r.val V.val = J t r.val g - (1 / 2 : ℂ) • J t r.val e := by
    rw [hV, J_sub_right r.property hg (he.smul (1 / 2 : ℂ)), J_smul_right]
  rw [hc, hj]
  change (CIntegrand t e g g - J t r.val g) +
    (((1 / 2 : ℂ) • CIntegrand t v.val v.val e - (1 / 2 : ℂ) • CIntegrand t e g e) +
      (1 / 2 : ℂ) • J t r.val e) = _
  module

end KdV
