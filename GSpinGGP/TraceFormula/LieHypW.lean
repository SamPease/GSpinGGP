/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.W1Untruncated
import GSpinGGP.TraceFormula.LuoTransfer
import GSpinGGP.TraceFormula.ConeTorus

/-!
# The geometric expansion near `1` when `W` is a hyperbolic plane

`geomAt_near_hypW`: for `W` a hyperbolic plane, `J(f) = m_geom(θ_f)` for `f ∈ ScuspTestFn d χ`
supported near `A_G(F)`.  The route (the special orthogonal group `SO(V)` alone, on its Lie
algebra):

1. **Descent and dictionary** (`exists_hypW_descent`, SORRY, own work).  With `W` a hyperbolic
   plane, `T_W = GSpin(W) ≅ G_m²` is central and split, `A_G = T_W × Z_V`, and
   `Φ(t, g) = t⁻¹ g` identifies `H(F)\G(F)/A_G(F)` with `U(F)SO(W)(F)\SO(V)(F)` (Hilbert 90).  Near
   `1`, `f` descends to `1_{ω_W} ⊗ φ_ω` on `so(W) ⊕ so(V)` (`χ ∘ exp = 1` on a small `ω_W`;
   Jacobians `≡ 1` on a small `ω`); `φ_ω` is very cuspidal (the proper parabolics of `G` are
   `GSpin(W) × P_V`); `K(f, x) = I(1_{ω_W}, φ_ω, Φ(x))` pointwise for compatible measures, so
   `J(f) = ∫ I(θ, φ_ω, g) dg` and the integrability of `K(f, ·)` (`distribJ_convergent`) passes to
   `I(θ, φ_ω, ·)`; and `m_geom(θ_f) = c_θ(0) c_{θ_{φ_ω}}(0)` (`Γ(G, H)` is the class of `1`;
   `(θ_f)_ω = θ_{φ_ω}` near `0`).
2. **Waldspurger 2010 Thm 7.9 untruncated** (`LuoDatum.integral_Ig_eq_Igeom`, from the axiom
   `waldspurger2010_thm_7_9`): `∫ I(θ, φ, g) dg = I(θ, φ)`.
3. **The geometric side for `W` a plane** (`Igeom_of_isHypPlane`, SORRY): `𝒯` is `{1}`, so
   `I(θ, φ) = c_θ(0) c_f(0)`.
-/

open MeasureTheory Topology Filter

noncomputable section

namespace GSpinGGP

namespace LuoDatum

variable {F : Type} [NontriviallyNormedField F] [PAdicField F] {L : LuoDatum F}
  {ψ : NontrivialAddChar F}

/-- **W1's `I(θ, f)` when `W` is a hyperbolic plane** (W1 §7.3, §7.9, evaluated).
The subtori of `H = SO(W) ≅ G_m` are `{1}` and `SO(W)`; `SO(W)` is split, so `A_T ≠ 1`
(condition (1)): for `Y ≠ 0` in `𝔥 ≅ F`, `T_Y = SO(W)` has non-compact `F`-points.  For `T = {1}`:
`W' = 0`, `W'' = W`, `V'' = V`, `d` is odd, and condition (4) is `d_an(V) = 1`, which holds since
`V = W ⊕ D ⊕ Z` with `W` and `Z` hyperbolic.  So `𝒯` is one class `{1}`.  For `T = {1}`: `|W(H, T)| = 1`, `𝔱 = 0` with
`ν(T) dY` the unit point mass (`IsExpCompatTW`), `0 ∈ 𝔱_♮`, `D^H(0) = 1` (`𝔥` abelian),
`Δ(0) = 1` (determinant on the zero space).  Hence `I(θ, f) = c_θ(0) c_f(0)`.
Status: SORRY (a computation). -/
theorem Igeom_of_isHypPlane (hW : IsHypPlane L.QW) (I : L.W1Input ψ) (θ : ↥L.soW → ℂ)
    (τ : ↥L.soV → ℂ) :
    I.Igeom θ τ = L.cThetaW ψ θ 0 * L.cFW ψ τ 0 := by
  sorry

end LuoDatum

namespace GGPData

variable {F : Type} [NontriviallyNormedField F] [PAdicField F] (ψ : NontrivialAddChar F)
  (d : GGPData F)

open LuoDatum

/-- **Descent near `1` to `(SO(V), SO(W))` when `W` is a hyperbolic plane** (Thesis
Prop 12.4.1(i) and Prop 12.1.1(iv), for this case; own work).  There is an invariant clopen
`Ω ∋ 1` such that for every `f ∈ ScuspTestFn d χ` supported in `Ω` there are data of
Waldspurger 2010 §7.2 for `d.luoOf` (`W1Input`), a quasi-character `θ` on `so(W)(F)` (the
indicator of a small lattice), a very cuspidal `φ` on `so(V)(F)` and its `θ_φ` (`τ`), with
* (i) `J(f) = ∫_{U(F)H(F)\SO(V)(F)} I(θ, φ, g) dg`;
* (ii) if `x ↦ K(f, x)` is integrable on `H(F)\G(F)/A_G(F)`, then `g ↦ I(θ, φ, g)` is
  integrable on `U(F)H(F)\SO(V)(F)`;
* (iii) `m_geom(θ_f) = c_θ(0) c_{θ_φ}(0)`.
Proof plan: `Φ(t, g) = t⁻¹ g` and Hilbert 90 (`quotHG_equiv`); shrink `ω` so that the Jacobians
of `exp` are `1` and `χ ∘ exp = 1` on `ω_W` (`F` is `p`-adic); then choose `ω_V` after `ω_W`, so
small that every `Y ∈ so(W)` with `Y + N ∈ Ad(g) ω_V` for some `N ∈ 𝔲`, `g ∈ SO(V)` lies in `ω_W`
(then `θ = 1_{ω_W}` acts as `1` in the kernel, which is needed to identify `K(f, ·)` with
`I(θ, φ_ω, ·)`); `H ∩ A_G exp(ω) = A_{G,H} exp(ω ∩ 𝔥⁰)` and `χ` is trivial on `A_{G,H}`; the kernel identity `K(f, x) = I(θ, φ_ω, Φ(x))` pointwise for
measures matched through `exp` and the Weil formula (no free constant); strong cuspidality of `f`
gives very cuspidality of `φ_ω`; the descent `(θ_f)_ω = θ_{φ_ω}` near `0` and the collapse of
`Γ(G, H)` to the class of `1` give (iii).  Obligations beyond the descent itself: a `W1Input` for
`d.luoOf` exists (W1 §7.2: a special lattice `R₀` of `V₀` and a lattice `R_Z` with `R₀ ⊕ R_Z`
special can be chosen; the measures exist), unproved here; and the regular germs of quasi-characters
on `so(V)` and `so(W)` are unique (Harish-Chandra 1999 Cor 5.10, as `germLie_unique_SO` for the
product), needed to match `c_θ(0) c_{θ_φ}(0)` with the germ of `θ_f` at `1`.  For `W` a plane,
`Γ(G, H)` is the class of `1`, so `m_geom(θ_f)` is the single regular germ of `θ_f` at `1`;
only its comparison with `c_θ(0) c_{θ_φ}(0)` uses Waldspurger's data.
Status: SORRY. -/
theorem exists_hypW_descent (hW : IsHypPlane d.QW) (χ : CentralCharOn d) :
    ∃ Ω : Set ↥d.G, IsInvariantClopen d Ω ∧ (1 : ↥d.G) ∈ Ω ∧
      ∀ f ∈ ScuspTestFn d χ, Function.support f ⊆ Ω →
        ∃ (I : d.luoOf.W1Input ψ) (θ : ↥d.luoOf.soW → ℂ) (φ τ : ↥d.luoOf.soV → ℂ),
          IsLieQuasiCharacter d.luoOf.SOW d.luoOf.soW d.luoOf.bW ψ θ ∧
          d.luoOf.IsVeryCuspidal φ ∧ d.luoOf.IsThetaFW1 ψ I.μG φ τ ∧
          distribJ d ψ f = ∫ q, I.Ig θ φ (CosetSpace.out d.luoOf.UHbar.subtype q) ∂I.m ∧
          (Integrable (fun q : d.HGQuot => kernelK d ψ f (d.repHG q)) d.weilMeasureHG →
            Integrable (fun q => I.Ig θ φ (CosetSpace.out d.luoOf.UHbar.subtype q)) I.m) ∧
          mGeom ψ d (thetaF d f) = d.luoOf.cThetaW ψ θ 0 * d.luoOf.cFW ψ τ 0 := by
  sorry

/-- **`geomAt_near` when `W` is a hyperbolic plane**, from the descent (`exists_hypW_descent`),
Waldspurger 2010 Thm 7.9 untruncated (`integral_Ig_eq_Igeom`, with the convergence of `J`,
`distribJ_convergent`), and the geometric side for `W` a plane (`Igeom_of_isHypPlane`). -/
theorem geomAt_near_hypW (hW : IsHypPlane d.QW) (χ : CentralCharOn d) :
    ∃ Ω : Set ↥d.G, IsInvariantClopen d Ω ∧ (1 : ↥d.G) ∈ Ω ∧
      ∀ f ∈ ScuspTestFn d χ, Function.support f ⊆ Ω →
        distribJ d ψ f = mGeom ψ d (thetaF d f) := by
  obtain ⟨Ω, hΩ, h1, hdesc⟩ := d.exists_hypW_descent ψ hW χ
  refine ⟨Ω, hΩ, h1, fun f hf hs => ?_⟩
  obtain ⟨I, θ, φ, τ, hθ, hφ, hτ, hJ, hint, hm⟩ := hdesc f hf hs
  have hW' : IsHypPlane d.luoOf.QW := hW
  have hV2 : ¬ IsHypPlane d.luoOf.QV := fun h => by
    have h1 := h.1
    have h2 := hW.1
    simp only [LuoDatum.V, LuoDatum.W, LuoDatum.Zs, Module.finrank_prod, Module.finrank_fin_fun]
      at h1 h2
    have : d.luoOf.m = d.m := rfl
    omega
  rw [hJ, hm,
    integral_Ig_eq_Igeom d.nondeg_QV hV2 I hθ hφ hτ (hint (d.distribJ_convergent χ ψ f hf)),
    Igeom_of_isHypPlane hW' I θ τ]

end GGPData

end GSpinGGP
