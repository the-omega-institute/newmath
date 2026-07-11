import BEDC.Derived.RHRoute.OCLSDSpectral

/-
ζ-free discharge of `OrbitCriticalReadback` (oracle conv_ff4ff126afd06e33, 2026-07-02).

`OrbitCriticalReadback` (an orbit's located point equals the critical embedding of its
height) is NOT the located-ζ wall — it is a ζ-free model-coupling gap: the syntax
readback `locatedFold s.term` and the orbit height `orbitHeight o` are accumulated by
two independent recursions with no built-in link. This module closes that gap, so the
whole RH residual collapses to
  `ZetaBridgeObligations ⟸ SpectralZeroIdentity + BindingObligation`,
with no free-standing bookkeeping obligation left on the ζ-free side.

Correctness note (oracle): do NOT make `GenState.point s = Crit.critical (orbitHeight o)`
definitional — `orbitHeight` depends on the orbit proof, `GenState.point` only on the
state (proof-relevance mismatch). Instead couple through a state-level `stateHeight`,
and prove `stateHeight s ~ orbitHeight o` by induction — via the `Orbit.rec` recursor
(propext-free; the equation compiler would leak propext on the indexed family).

After this brick: ζ-free scaffolding stops. The only remaining content is the
Hilbert–Pólya wall `SpectralZeroIdentity` (spectrum = true ζ zeros).
-/

namespace BEDC.Derived.RHRoute.OCLSDCriticalCoupling

open BEDC.Derived.RHRoute.OCLSDSpectral
open BEDC.Derived.RHRoute.LocatedGenerationTower
open BEDC.Derived.RHRoute.ZeroGenerationInitiality

universe u

variable {sig : RHFreeZeroSignature} {LR : Type u}
  {M : LocatedZeroModel sig LR} {K : DynamicsTypes}

/-- Congruence law for the height addition (kept separate from the landed
`TickHeightKit` API). -/
structure HeightAddLaws (C : TickHeightKit K) where
  add_congr : {a a' b b' : C.Height} →
    C.HEq.Eqv a a' → C.HEq.Eqv b b' → C.HEq.Eqv (C.add a b) (C.add a' b')

/-- ζ-free coupling between the syntactic located-point readback, a state-level
accumulated height, and the tick-level height. The missing link to discharge
`OrbitCriticalReadback`. Says nothing about ζ zeros. -/
structure StateHeightCoupling (D : GenerationDynamics M K) (C : TickHeightKit K)
    (PEq : PointEquality (LocatedComplex LR)) (Crit : CriticalEmbedding C PEq) where
  stateHeight : GenState M K → C.Height
  point_eq_stateHeight : (s : GenState M K) →
    PEq.Eqv (GenState.point s) (Crit.critical (stateHeight s))
  init_height : C.HEq.Eqv (stateHeight (initState D)) C.zero
  step_height : (s : GenState M K) → (g : LegalGenerationStep D s) →
    C.HEq.Eqv (stateHeight (step D s g))
      (C.add (stateHeight s) (C.tickHeight g.raw))

/-- Every forward orbit's endpoint state-height equals the orbit's cumulative height.
By `Orbit.rec` induction (propext-free). -/
noncomputable def stateHeight_eq_orbitHeight
    {D : GenerationDynamics M K} {C : TickHeightKit K}
    {PEq : PointEquality (LocatedComplex LR)} {Crit : CriticalEmbedding C PEq}
    (HL : HeightAddLaws C) (CC : StateHeightCoupling D C PEq Crit) :
    {s : GenState M K} → (o : Orbit D s) →
      C.HEq.Eqv (CC.stateHeight s) (orbitHeight C o) :=
  fun {_} o =>
    Orbit.rec
      (motive := fun s o => C.HEq.Eqv (CC.stateHeight s) (orbitHeight C o))
      CC.init_height
      (fun _ g ih =>
        C.HEq.trans (CC.step_height _ g)
          (HL.add_congr ih (C.HEq.refl (C.tickHeight g.raw))))
      o

/-- **Payoff**: a `StateHeightCoupling` discharges `OrbitCriticalReadback`, ζ-free. -/
noncomputable def orbitCriticalReadback_from_stateHeight
    {D : GenerationDynamics M K} {C : TickHeightKit K}
    {PEq : PointEquality (LocatedComplex LR)}
    (PEL : PointEqLaws PEq) (HL : HeightAddLaws C)
    {Crit : CriticalEmbedding C PEq}
    (CC : StateHeightCoupling D C PEq Crit) :
    OrbitCriticalReadback C D PEq Crit where
  point_eq_critical := fun {s} o =>
    PEL.trans (CC.point_eq_stateHeight s)
      (Crit.respects_height (stateHeight_eq_orbitHeight HL CC o))

/-- The full bridge now needs only `SpectralZeroIdentity` + `BindingObligation`
(+ the ζ-free coupling), no free-standing `OrbitCriticalReadback` obligation. -/
noncomputable def zetaBridge_from_spectral_coupled
    {D : GenerationDynamics M K} {C : TickHeightKit K}
    {PEq : PointEquality (LocatedComplex LR)}
    (PEL : PointEqLaws PEq) (HL : HeightAddLaws C)
    {Crit : CriticalEmbedding C PEq}
    {E : LocatedZetaEvaluator (LocatedComplex LR) (LocatedComplex LR)}
    (CC : StateHeightCoupling D C PEq Crit)
    (SZ : SpectralZeroIdentity C D PEq Crit E)
    (B : BindingObligation E) :
    ZetaBridgeObligations D PEq E :=
  zetaBridge_from_spectral C PEL
    (orbitCriticalReadback_from_stateHeight PEL HL CC) SZ B

/-- A concrete ζ-free model where the syntax also carries a height semantics, and the
point readback commutes with it through the critical embedding. Discharges the coupling
without a raw obligation. `heightFold := GeneratedZero.fold heightAlg`. -/
structure SyntaxHeightCoupledModel (M : LocatedZeroModel sig LR)
    (D : GenerationDynamics M K) (C : TickHeightKit K)
    (PEq : PointEquality (LocatedComplex LR)) (Crit : CriticalEmbedding C PEq) where
  heightAlg : ZeroAlgebra sig C.Height
  fold_commutes : (t : GeneratedZero sig) →
    PEq.Eqv (locatedFold M t) (Crit.critical (GeneratedZero.fold heightAlg t))
  initTerm_height :
    C.HEq.Eqv (GeneratedZero.fold heightAlg D.initTerm) C.zero
  nextTerm_height : (t : GeneratedZero sig) → (raw : RawGenerationStep K) →
    C.HEq.Eqv (GeneratedZero.fold heightAlg (D.nextTerm t raw))
      (C.add (GeneratedZero.fold heightAlg t) (C.tickHeight raw))

/-- A `SyntaxHeightCoupledModel` induces a `StateHeightCoupling` (projection-only:
`stateHeight s := heightFold s.term`; the fields discharge by the model fields). -/
def stateHeightCoupling_from_syntaxHeight
    {D : GenerationDynamics M K} {C : TickHeightKit K}
    {PEq : PointEquality (LocatedComplex LR)} {Crit : CriticalEmbedding C PEq}
    (SH : SyntaxHeightCoupledModel M D C PEq Crit) :
    StateHeightCoupling D C PEq Crit where
  stateHeight := fun s => GeneratedZero.fold SH.heightAlg s.term
  point_eq_stateHeight := fun s => SH.fold_commutes s.term
  init_height := SH.initTerm_height
  step_height := fun s g => SH.nextTerm_height s.term g.raw

/-- End-to-end: a concrete syntax-height model discharges `OrbitCriticalReadback`. -/
noncomputable def orbitCriticalReadback_from_syntaxHeight
    {D : GenerationDynamics M K} {C : TickHeightKit K}
    {PEq : PointEquality (LocatedComplex LR)}
    (PEL : PointEqLaws PEq) (HL : HeightAddLaws C)
    {Crit : CriticalEmbedding C PEq}
    (SH : SyntaxHeightCoupledModel M D C PEq Crit) :
    OrbitCriticalReadback C D PEq Crit :=
  orbitCriticalReadback_from_stateHeight PEL HL
    (stateHeightCoupling_from_syntaxHeight SH)

/-- Non-vacuity payoff: the orbit height is endpoint-determined — any two orbits to the
same state have equal height. Resolves the proof-relevance concern. -/
noncomputable def orbitHeight_path_coherent
    {D : GenerationDynamics M K} {C : TickHeightKit K}
    {PEq : PointEquality (LocatedComplex LR)} {Crit : CriticalEmbedding C PEq}
    (HL : HeightAddLaws C) (CC : StateHeightCoupling D C PEq Crit)
    {s : GenState M K} (o₁ o₂ : Orbit D s) :
    C.HEq.Eqv (orbitHeight C o₁) (orbitHeight C o₂) :=
  C.HEq.trans
    (C.HEq.symm (stateHeight_eq_orbitHeight HL CC o₁))
    (stateHeight_eq_orbitHeight HL CC o₂)

end BEDC.Derived.RHRoute.OCLSDCriticalCoupling
