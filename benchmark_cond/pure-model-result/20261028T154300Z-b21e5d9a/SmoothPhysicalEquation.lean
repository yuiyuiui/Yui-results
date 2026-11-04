import PhysicalVectorFieldSmooth
import PhysicalCoefficientDerivative
noncomputable section
open scoped ComplexConjugate ENNReal
open MeasureTheory
namespace KdV
set_option maxHeartbeats 800000

theorem sobolev_val_add {s : ℝ} (f g : Sobolev s) : (f + g).val = f.val + g.val := rfl

theorem physicalRHS_coefficient (f : Fourier) (k : ℤ) :
    physicalRHS f k = Complex.I * (k : ℂ) ^ 3 * f k +
      (1 / 2 : ℂ) * (Complex.I * (k : ℂ)) * product f f k := by
  simp only [physicalRHS, derivative, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  ring_nf
  rw [Complex.I_pow_three]
  ring

def spatialPath {T : ℝ} {u : ℝ → Fourier} (hT : 0 ≤ T)
    (hAll : ∀ s : ℝ, SobolevContinuousOn s T u) (n : ℕ) : ℝ → Sobolev ((n + 1 : ℕ) : ℝ) :=
  sobolevExtension hT u (hAll ((n + 1 : ℕ) : ℝ))

theorem continuous_spatialPath {T : ℝ} {u : ℝ → Fourier} (hT : 0 ≤ T)
    (hAll : ∀ s : ℝ, SobolevContinuousOn s T u) (n : ℕ) : Continuous (spatialPath hT hAll n) :=
  continuous_sobolevExtension hT _

theorem spatialPath_val_on {T : ℝ} {u : ℝ → Fourier} (hT : 0 ≤ T)
    (hAll : ∀ s : ℝ, SobolevContinuousOn s T u) (n : ℕ) {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    (spatialPath hT hAll n t).val = u t := sobolevExtension_val_on hT _ ht

/-- The coefficient Duhamel equation is an actual Bochner integral equation
 in every positive integer Sobolev space for an all-regularity flow. -/
theorem spatial_physical_integral {T : ℝ} {f : Fourier} {u : ℝ → Fourier}
    (hT : 0 ≤ T) (hu : KdVSolution 2 T f u) (hAll : ∀ s : ℝ, SobolevContinuousOn s T u)
    (n : ℕ) {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    spatialPath hT hAll n t = spatialPath hT hAll n 0 +
      ∫ r : ℝ in (0 : ℝ)..t, physicalVectorField n (spatialPath hT hAll (n + 3) r) := by
  let U := spatialPath hT hAll n
  let F := fun r => physicalVectorField n (spatialPath hT hAll (n + 3) r)
  have hUC : Continuous U := continuous_spatialPath hT hAll n
  have hFC : Continuous F := (continuous_physicalVectorField n).comp (continuous_spatialPath hT hAll (n + 3))
  have hi : IntervalIntegrable F volume 0 t := hFC.intervalIntegrable 0 t
  apply Sobolev.ext
  rw [sobolev_val_add, sobolev_integral_val hi]
  funext k
  have hcU : ContinuousOn (fun r : ℝ => u r k) (Set.Icc 0 t) := by
    apply (((coefficientMap ((n + 1 : ℕ) : ℝ) k).continuous.comp hUC).continuousOn).congr
    intro r hr
    change u r k = (U r).val k
    rw [spatialPath_val_on hT hAll n ⟨hr.1, hr.2.trans ht.2⟩]
  have hcF : Continuous (fun r : ℝ => (F r).val k) :=
    (coefficientMap ((n + 1 : ℕ) : ℝ) k).continuous.comp hFC
  have hd : ∀ r ∈ Set.Ioo 0 t, HasDerivAt (fun s : ℝ => u s k) ((F r).val k) r := by
    intro r hr
    have hrT : r ∈ Set.Ioo 0 T := ⟨hr.1, hr.2.trans_le ht.2⟩
    have h := physical_coefficient_hasDerivAt hT hu hrT k
    have hfVal : (F r).val = physicalRHS (u r) := by
      rw [physicalVectorField_val, spatialPath_val_on hT hAll (n + 3) ⟨hrT.1.le, hrT.2.le⟩]
    rwa [hfVal, physicalRHS_coefficient]
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 hcU hd (hcF.intervalIntegrable 0 t)
  change (spatialPath hT hAll n t).val k = (spatialPath hT hAll n 0).val k + ∫ r : ℝ in (0 : ℝ)..t, (F r).val k
  rw [spatialPath_val_on hT hAll n ht, spatialPath_val_on hT hAll n ⟨le_rfl, hT⟩, hFTC]
  ring

end KdV
