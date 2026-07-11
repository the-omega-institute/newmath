import BEDC.Derived.RHRoute.LocatedGenerationTower

/-
OCLSD spectral reformulation of the RH bridge (oracle conv_ff4ff126afd06e33, 2026-07-02).

The oracle's strategic move: do NOT target the strong evaluator binding
`carrierEval = trueEval`. Target the WEAKER, more RH-aligned **spectral identity**
  γ ∈ Spec(H_OCLSD)  ⟺  ζ(1/2 + iγ) = 0,
where `H_OCLSD` is the diagonal operator whose eigenvalues are the cumulative
angular heights of the forward OCLSD orbits (Hilbert–Pólya, OCLSD form).

This module builds it 0-axiom and **proves** that the spectral identity (plus a
ζ-free orbit→critical-line readback and a binding stub) IMPLIES the full
`LocatedGenerationTower.ZetaBridgeObligations`. So the entire RH residual can be
routed through a single spectral identity that never evaluates ζ pointwise.

Everything except the spectral identity itself is ζ-free. The orbit height uses the
generated `Orbit.rec` (propext-free; the equation compiler would leak propext on the
indexed family, the recursor does not) and is `noncomputable` only because bare
recursors have no compiled code — the axiom footprint stays empty.
-/

namespace BEDC.Derived.RHRoute.OCLSDSpectral

open BEDC.Derived.RHRoute.LocatedGenerationTower
open BEDC.Derived.RHRoute.ZeroGenerationInitiality

universe u

/-- Type-valued equivalence kit (propext-free). -/
structure EqKit (A : Type u) where
  Eqv : A → A → Type u
  refl : (x : A) → Eqv x x
  symm : {x y : A} → Eqv x y → Eqv y x
  trans : {x y z : A} → Eqv x y → Eqv y z → Eqv x z

/-- Per-tick angular-height accumulation kit: the height type + its equality +
the height contributed by one legal tick. -/
structure TickHeightKit (K : DynamicsTypes) where
  Height : Type u
  HEq : EqKit Height
  zero : Height
  add : Height → Height → Height
  tickHeight : RawGenerationStep K → Height

variable {sig : RHFreeZeroSignature} {LR : Type u}
  {M : LocatedZeroModel sig LR} {K : DynamicsTypes}

/-- Cumulative height along a forward orbit, via the recursor (propext-free). -/
noncomputable def orbitHeight (C : TickHeightKit K)
    {D : GenerationDynamics M K} {s : GenState M K} (o : Orbit D s) : C.Height :=
  Orbit.rec (motive := fun _ _ => C.Height)
    C.zero
    (fun _ g ih => C.add ih (C.tickHeight g.raw))
    o

/-- An orbit-indexed basis element: a state with an orbit reaching it. -/
structure OrbitBasis (D : GenerationDynamics M K) where
  state : GenState M K
  orbit : Orbit D state

/-- Point spectrum of `H_OCLSD` at height `γ`: a basis orbit whose cumulative
height is `Eqv`-equal to `γ`. Type-valued (no `Set`/`∃`). -/
def PointSpectrum (C : TickHeightKit K) (D : GenerationDynamics M K)
    (γ : C.Height) : Type u :=
  Sigma (fun b : OrbitBasis D => C.HEq.Eqv (orbitHeight C b.orbit) γ)

/-- Every forward orbit sits in the point spectrum at its own height. -/
noncomputable def orbit_in_pointSpectrum (C : TickHeightKit K)
    {D : GenerationDynamics M K} {s : GenState M K} (o : Orbit D s) :
    PointSpectrum C D (orbitHeight C o) :=
  ⟨{ state := s, orbit := o }, C.HEq.refl (orbitHeight C o)⟩

/-- Located-real point-equality laws (equivalence). -/
structure PointEqLaws (PEq : PointEquality (LocatedComplex LR)) where
  refl : (x : LocatedComplex LR) → PEq.Eqv x x
  symm : {x y : LocatedComplex LR} → PEq.Eqv x y → PEq.Eqv y x
  trans : {x y z : LocatedComplex LR} → PEq.Eqv x y → PEq.Eqv y z → PEq.Eqv x z

/-- Embedding of spectral heights into located-complex points, `γ ↦ 1/2 + iγ`. -/
structure CriticalEmbedding (C : TickHeightKit K)
    (PEq : PointEquality (LocatedComplex LR)) where
  critical : C.Height → LocatedComplex LR
  respects_height : {γ δ : C.Height} → C.HEq.Eqv γ δ →
    PEq.Eqv (critical γ) (critical δ)

/-- ζ-free bridge: an orbit's located point equals the critical embedding of its
height. Dischargeable from fixed-half closure (generated points are `1/2 + iγ`). -/
structure OrbitCriticalReadback (C : TickHeightKit K)
    (D : GenerationDynamics M K)
    (PEq : PointEquality (LocatedComplex LR))
    (Crit : CriticalEmbedding C PEq) where
  point_eq_critical : {s : GenState M K} → (o : Orbit D s) →
    PEq.Eqv (GenState.point s) (Crit.critical (orbitHeight C o))

/-- The Hilbert–Pólya wall as a **spectral identity**, weaker than evaluator
binding: OCLSD spectral heights ⟺ true ζ zeros on the critical line. -/
structure SpectralZeroIdentity (C : TickHeightKit K)
    (D : GenerationDynamics M K)
    (PEq : PointEquality (LocatedComplex LR))
    (Crit : CriticalEmbedding C PEq)
    (E : LocatedZetaEvaluator (LocatedComplex LR) (LocatedComplex LR)) where
  spec_to_zero_at : (z : LocatedComplex LR) → (γ : C.Height) →
    PEq.Eqv (Crit.critical γ) z → PointSpectrum C D γ → TrueZetaZero E z
  zero_to_spec_at : (z : LocatedComplex LR) → TrueZetaZero E z →
    Sigma (fun γ : C.Height =>
      Prod (PointSpectrum C D γ) (PEq.Eqv (Crit.critical γ) z))

/-- Soundness from the spectral identity: every generated point is a true ζ zero. -/
noncomputable def soundness_from_spectral (C : TickHeightKit K)
    {D : GenerationDynamics M K}
    {PEq : PointEquality (LocatedComplex LR)}
    (PEL : PointEqLaws PEq)
    {Crit : CriticalEmbedding C PEq}
    {E : LocatedZetaEvaluator (LocatedComplex LR) (LocatedComplex LR)}
    (OCR : OrbitCriticalReadback C D PEq Crit)
    (SZ : SpectralZeroIdentity C D PEq Crit E)
    (z : LocatedComplex LR) (gp : GeneratedPoint D PEq z) :
    TrueZetaZero E z :=
  match gp with
  | ⟨_, o, point_to_z⟩ =>
      SZ.spec_to_zero_at z (orbitHeight C o)
        (PEL.trans (PEL.symm (OCR.point_eq_critical o)) point_to_z)
        (orbit_in_pointSpectrum C o)

/-- Completeness from the spectral identity: every true ζ zero is generated. -/
noncomputable def completeness_from_spectral (C : TickHeightKit K)
    {D : GenerationDynamics M K}
    {PEq : PointEquality (LocatedComplex LR)}
    (PEL : PointEqLaws PEq)
    {Crit : CriticalEmbedding C PEq}
    {E : LocatedZetaEvaluator (LocatedComplex LR) (LocatedComplex LR)}
    (OCR : OrbitCriticalReadback C D PEq Crit)
    (SZ : SpectralZeroIdentity C D PEq Crit E)
    (z : LocatedComplex LR) (hz : TrueZetaZero E z) :
    GeneratedPoint D PEq z :=
  match SZ.zero_to_spec_at z hz with
  | ⟨_, ⟨b, h_eq_γ⟩, critγ_to_z⟩ =>
      ⟨b.state, b.orbit,
        PEL.trans (OCR.point_eq_critical b.orbit)
          (PEL.trans (Crit.respects_height h_eq_γ) critγ_to_z)⟩

/-- **The reformulation payoff**: a spectral identity (Hilbert–Pólya form) plus a
ζ-free orbit→critical-line readback and a binding stub yields the full
`ZetaBridgeObligations`. So the RH residual can be carried by a single spectral
identity that never evaluates ζ pointwise. -/
noncomputable def zetaBridge_from_spectral (C : TickHeightKit K)
    {D : GenerationDynamics M K}
    {PEq : PointEquality (LocatedComplex LR)}
    (PEL : PointEqLaws PEq)
    {Crit : CriticalEmbedding C PEq}
    {E : LocatedZetaEvaluator (LocatedComplex LR) (LocatedComplex LR)}
    (OCR : OrbitCriticalReadback C D PEq Crit)
    (SZ : SpectralZeroIdentity C D PEq Crit E)
    (B : BindingObligation E) :
    ZetaBridgeObligations D PEq E :=
  { binding := B
    completeness := { complete := fun z hz => completeness_from_spectral C PEL OCR SZ z hz }
    soundness := { sound := fun z gp => soundness_from_spectral C PEL OCR SZ z gp } }

end BEDC.Derived.RHRoute.OCLSDSpectral
