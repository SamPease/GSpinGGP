import GSpinGGP.Foundations.GSpinLipschitz
import TauCeti.LinearAlgebra.CliffordAlgebra.Lipschitz.ReverseNorm

/-!
# The commutator sign on the centralizer of `P(x)`

For `x, g ∈ GSpin(V)` such that `P(g)` commutes with `P(x)` in `SO(V)`, the commutator
`g x g⁻¹ x⁻¹` lies in the kernel of `P`, which is the scalars, and its Clifford norm is `1`, so
`g x g⁻¹ = c x` with `c = ±1` (`exists_conj_eq_smul`). This sign is the obstruction measured by the
determinant conditions in `steinberg_centralizer_connected` (Thesis §6.1, connectedness of
centralizers of semisimple elements, after Steinberg).
-/

open CliffordAlgebra

namespace GSpinGGP

namespace CentralizerSign

variable {K : Type*} [Field K] [Invertible (2 : K)]
  {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

/-- If `P(g)` commutes with `P(x)`, then `g x g⁻¹ = c x` for a scalar `c` with `c² = 1`. -/
theorem exists_conj_eq_smul (hQ : IsNondeg Q) {g x : GSpin Q}
    (h : Commute (specP Q g) (specP Q x)) :
    ∃ c : Kˣ, c ^ 2 = 1 ∧ g * x * g⁻¹ = scalarGSpin Q c * x := by
  have hker : g * x * g⁻¹ * x⁻¹ ∈ (specP Q).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, h.eq]
    group
  rw [ker_specP hQ] at hker
  obtain ⟨c, hc⟩ := hker
  have hconj : g * x * g⁻¹ = scalarGSpin Q c * x := by
    rw [hc]; group
  refine ⟨c, ?_, hconj⟩
  rcases subsingleton_or_nontrivial V with hV | hV
  · -- `V = 0`: `P` is trivial, so `g` and `x` are scalars and commute
    have hs : ∀ y : GSpin Q, y ∈ (scalarGSpin Q).range := fun y => by
      rw [← ker_specP hQ, MonoidHom.mem_ker]
      ext v
      simp [Subsingleton.elim v 0]
    obtain ⟨a, rfl⟩ := hs g
    obtain ⟨b, rfl⟩ := hs x
    have h1 : scalarGSpin Q c = 1 := by
      have : scalarGSpin Q a * scalarGSpin Q b * (scalarGSpin Q a)⁻¹ = scalarGSpin Q b := by
        rw [← map_inv, ← map_mul, ← map_mul, mul_comm a b, mul_assoc, mul_inv_cancel, mul_one]
      rw [this] at hconj
      simpa using hconj.symm
    have hinj : Function.Injective (scalarGSpin Q) := by
      intro a b hab
      have := congrArg (fun y : GSpin Q => ((y : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) hab
      simp only [scalarGSpin, MonoidHom.coe_mk, OneHom.coe_mk, Units.coe_map,
        RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass] at this
      exact Units.ext (algebraMap_injective Q this)
    rw [hinj (h1.trans (map_one _).symm), one_pow]
  · -- Clifford norm: `N(c x) = c² N(x)` and `N(g x g⁻¹) = N(x)`
    have hQ' := (isNondeg_iff_nondegenerate Q).1 hQ
    obtain ⟨v, hv⟩ := hQ'.exists_isUnit
    have hL : ∀ y : GSpin Q, (y : (CliffordAlgebra Q)ˣ) ∈ lipschitzGroup Q := fun y =>
      ((mem_GSpin_iff_mem_lipschitzGroup Q hQ ⟨v, hv⟩ y).1 y.2).1
    let L : GSpin Q →* lipschitzGroup Q :=
      { toFun := fun y => ⟨y, hL y⟩, map_one' := rfl, map_mul' := fun _ _ => rfl }
    have hN := cliffordNorm_eq_sq_mul_of_coe_eq_algebraMap_mul (Q := Q)
      (x := L x) (y := L (g * x * g⁻¹)) (c := c) (by
        change (((g * x * g⁻¹ : GSpin Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) = _
        rw [hconj]
        simp [scalarGSpin, L])
    simp only [map_mul, map_inv] at hN
    rw [mul_comm (cliffordNorm Q (L g)), mul_assoc, mul_inv_cancel, mul_one] at hN
    exact mul_eq_right.mp hN.symm

/-- For an eigenvector `v` of `P(x)` with eigenvalue `ε`: `x v = ε v x` in `C(V)`. -/
theorem mul_ι_of_specP_eq_smul (x : GSpin Q) {v : V} {ε : K} (hv : specP Q x v = ε • v) :
    ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * ι Q v =
      algebraMap K (CliffordAlgebra Q) ε * (ι Q v * ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) := by
  have h := ι_specP x v
  rw [hv, map_smul, Algebra.smul_def] at h
  have h2 := congrArg (· * ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) h
  simp only [mul_assoc, Units.inv_mul, mul_one] at h2
  rw [← h2]

/-- For a list of eigenvectors `w` of `P(x)` with eigenvalues `ε w`, the product `∏ w` satisfies
`x (∏ w) = (∏ ε w) (∏ w) x`. -/
theorem mul_prod_ι_of_specP_eq_smul (x : GSpin Q) (ε : V → K) :
    ∀ (l : List V), (∀ w ∈ l, specP Q x w = ε w • w) →
      ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * (l.map (ι Q)).prod =
        algebraMap K (CliffordAlgebra Q) (l.map ε).prod *
          ((l.map (ι Q)).prod * ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q))
  | [], _ => by simp
  | w :: t, h => by
    have hw := mul_ι_of_specP_eq_smul x (h w (by simp))
    have ht := mul_prod_ι_of_specP_eq_smul x ε t (fun w' hw' => h w' (by simp [hw']))
    set X := ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)
    set P := (t.map (ι Q)).prod
    simp only [List.map_cons, List.prod_cons, map_mul]
    calc X * (ι Q w * P) = (X * ι Q w) * P := (mul_assoc _ _ _).symm
      _ = algebraMap K _ (ε w) * (ι Q w * (X * P)) := by rw [hw]; simp only [mul_assoc]
      _ = algebraMap K _ (ε w) * (ι Q w * (algebraMap K _ (t.map ε).prod * (P * X))) := by
          rw [ht]
      _ = algebraMap K _ (ε w) * algebraMap K _ (t.map ε).prod * (ι Q w * P * X) := by
          rw [Algebra.left_comm]; simp only [mul_assoc]

/-! ### Sign-trivial rotations -/

/-- `σ ∈ SO(V)` is *sign-trivial* for `x` if every lift of `σ` to `GSpin(V)` commutes with `x`. -/
def SignTrivial (x : GSpin Q) (σ : V ≃ₗ[K] V) : Prop :=
  ∀ g : GSpin Q, specP Q g = σ → Commute g x

/-- Lifts differ by scalars, so one lift commuting with `x` makes `σ` sign-trivial. -/
theorem signTrivial_of_lift (hQ : IsNondeg Q) {x g : GSpin Q} (hg : Commute g x) :
    SignTrivial x (specP Q g) := by
  intro g' hg'
  have hker : g' * g⁻¹ ∈ (specP Q).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hg', mul_inv_cancel]
  rw [ker_specP hQ] at hker
  obtain ⟨c, hc⟩ := hker
  have hcomm : Commute (scalarGSpin Q c) x := by
    refine Subtype.ext (Units.ext ?_)
    simp [scalarGSpin, Algebra.commutes]
  have : g' = scalarGSpin Q c * g := by rw [hc]; group
  rw [this]
  exact hcomm.mul_left hg

/-- Sign-triviality is multiplicative, given a lift of the second factor. -/
theorem SignTrivial.mul {x : GSpin Q} {σ τ : V ≃ₗ[K] V} (hσ : SignTrivial x σ)
    (hτ : SignTrivial x τ) (hlift : ∃ h : GSpin Q, specP Q h = τ) : SignTrivial x (σ * τ) := by
  obtain ⟨h, hh⟩ := hlift
  intro g hg
  have h1 : specP Q (g * h⁻¹) = σ := by
    rw [map_mul, map_inv, hg, hh, mul_inv_cancel_right]
  have : g = (g * h⁻¹) * h := by group
  rw [this]
  exact (hσ _ h1).mul_left (hτ h hh)

/-- **Squares are sign-trivial**: if `P(b)` commutes with `P(x)`, then `P(b)²` is sign-trivial
(the sign of `b` is `±1` and squares to `1`). -/
theorem signTrivial_sq (hQ : IsNondeg Q) {x b : GSpin Q} (hb : Commute (specP Q b) (specP Q x)) :
    SignTrivial x (specP Q b ^ 2) := by
  obtain ⟨c, hc2, hc⟩ := exists_conj_eq_smul hQ hb
  have hcb : Commute (scalarGSpin Q c) b := by
    refine Subtype.ext (Units.ext ?_)
    simp [scalarGSpin, Algebra.commutes]
  have hb2 : Commute (b ^ 2) x := by
    have hbx : b * x = scalarGSpin Q c * x * b := by
      rw [← hc]; group
    rw [Commute, SemiconjBy, pow_two]
    calc b * b * x = b * (scalarGSpin Q c * x * b) := by rw [mul_assoc, hbx]
      _ = scalarGSpin Q c * (b * x) * b := by
          rw [← mul_assoc, ← mul_assoc, ← hcb.eq]; group
      _ = scalarGSpin Q c * (scalarGSpin Q c * x * b) * b := by rw [hbx]
      _ = scalarGSpin Q (c ^ 2) * x * (b * b) := by rw [map_pow, pow_two]; group
      _ = x * (b * b) := by rw [hc2, map_one, one_mul]
  rw [← map_pow]
  exact signTrivial_of_lift hQ hb2

end CentralizerSign

end GSpinGGP
