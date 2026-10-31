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

theorem T006 (n : ℕ) (E : Set (GPEucl n))  :
    ∀ (B : Set ℝ) (ρ η : ℝ), B.Nonempty → 0 ≤ ρ →
  (∀ b ∈ B, ∀ b' ∈ B, |b - b'| ≤ ρ) → 0 < η →
  BddAbove B ∧ BddBelow B ∧ IsLUB B (sSup B) ∧ IsGLB B (sInf B) ∧
  sSup B - sInf B ≤ ρ ∧
  B ⊆ Set.Ioo (sInf B - η / 2) (sSup B + η / 2) ∧
  (sInf B - η / 2 < sSup B + η / 2) ∧
  ((sSup B + η / 2) - (sInf B - η / 2) ≤ ρ + η) := by
  intro B ρ η hB hρ hpair hη
  obtain ⟨b₀, hb₀⟩ := hB
  have habove : BddAbove B := by
    refine ⟨b₀ + ρ, ?_⟩
    intro b hb
    have h := (abs_le.mp (hpair b hb b₀ hb₀)).2
    linarith
  have hbelow : BddBelow B := by
    refine ⟨b₀ - ρ, ?_⟩
    intro b hb
    have h := (abs_le.mp (hpair b hb b₀ hb₀)).1
    linarith
  have hlub : IsLUB B (sSup B) := isLUB_csSup ⟨b₀, hb₀⟩ habove
  have hglb : IsGLB B (sInf B) := isGLB_csInf ⟨b₀, hb₀⟩ hbelow
  have hsup : ∀ b' ∈ B, sSup B ≤ b' + ρ := by
    intro b' hb'
    apply hlub.2
    intro b hb
    have h := (abs_le.mp (hpair b hb b' hb')).2
    linarith
  have hlower : sSup B - ρ ≤ sInf B := by
    apply hglb.2
    intro b hb
    have h := hsup b hb
    linarith
  have hdiam : sSup B - sInf B ≤ ρ := by linarith
  have hcontain : B ⊆ Set.Ioo (sInf B - η / 2) (sSup B + η / 2) := by
    intro b hb
    have hlo : sInf B ≤ b := hglb.1 hb
    have hhi : b ≤ sSup B := hlub.1 hb
    constructor <;> linarith
  have horder : sInf B ≤ sSup B := le_trans (hglb.1 hb₀) (hlub.1 hb₀)
  refine ⟨habove, hbelow, hlub, hglb, hdiam, hcontain, ?_, ?_⟩
  · linarith
  · linarith

#check @T006
#print axioms T006

end Translation
