import BEDC.Derived.RHRoute.OCLSDPhaseAlgebra

/-
Shared prime-atom adapter: OCLSD phase route ↔ Weil geometric route (oracle + codex
consensus, 2026-07-02).

Adversarial consensus verdict on "connect OCLSD tick to the Weil geometric side":
BOOKKEEPING / shared-source ADAPTER, NOT a wall-advance. Two facts pinned it:
  * `Weil positivity ≢ SpectralZeroIdentity` — they are two DISTINCT analytic gates;
    feeding the Weil geometric side does NOT inhabit `Spec(H_OCLSD) = ζ zeros`.
  * The correct common object is NOT `readPZGPhase = WeilLocatedTerm` (wrong layers)
    but the shared **prime-log atom stream** `(p,k)`: the OCLSD phase character and the
    Weil geometric test-function term BOTH factor through the same atoms.

So this module builds exactly the thin, honest thing and stops: the shared atom stream,
a proof that the OCLSD phase readback factors through it, and a Weil-geometric evaluator
over the same atoms — a shared-source dictionary letting the OCLSD generativity route
and the existing Weil finite-certificate route consume one prime source. It advances
NO analytic gate: the wall (`SpectralZeroIdentity` / global Weil positivity ⟹ RH) is
untouched and remains the user-decision / located-ζ content.
-/

namespace BEDC.Derived.RHRoute.OCLSDWeilGeometricAdapter

open BEDC.Derived.RHRoute.OCLSDPhaseAlgebra

/-- The shared prime-log atom `(p,k)`: prime id + Fibonacci index. Its log-position is
`F_k · log p` (kept symbolic — the factorization is ζ-free). This is the single object
both the OCLSD phase character and the Weil geometric term factor through. -/
structure PrimeLogAtom where
  prime : Nat
  fibIndex : Nat

/-- OCLSD register row → its prime-log atom stream. -/
def atomStream : PZGRow → List PrimeLogAtom
  | PZGRow.nil => []
  | PZGRow.cons p k rest => { prime := p, fibIndex := k } :: atomStream rest

/-- Phase-character evaluation over an atom stream. -/
def phaseOfAtoms (A : FormalPhaseAlgebra) : List PrimeLogAtom → A.Phase
  | [] => A.one
  | a :: rest => A.mul (A.primePhase a.prime a.fibIndex) (phaseOfAtoms A rest)

/-- The OCLSD phase readback factors through the shared atom stream (ζ-free,
propext-free via `congrArg`). This is the "phase side" of the shared source. -/
theorem readPZGPhase_factors (A : FormalPhaseAlgebra) :
    ∀ row : PZGRow, readPZGPhase A row = phaseOfAtoms A (atomStream row)
  | PZGRow.nil => rfl
  | PZGRow.cons p k rest =>
      congrArg (A.mul (A.primePhase p k)) (readPZGPhase_factors A rest)

/-- A Weil geometric-side evaluator over the SAME atom stream (the test-function side).
Abstract interface; a concrete Weil route supplies the atom weight. The point is only
that it consumes the identical prime-atom source, not that its value equals the phase. -/
structure WeilGeometricEvaluator where
  Value : Type
  weilAtom : PrimeLogAtom → Value
  combine : Value → Value → Value
  unit : Value

/-- Weil geometric-side evaluation over an atom stream. -/
def weilOfAtoms (W : WeilGeometricEvaluator) : List PrimeLogAtom → W.Value
  | [] => W.unit
  | a :: rest => W.combine (W.weilAtom a) (weilOfAtoms W rest)

/-- The shared-source adapter: the OCLSD phase route and a Weil geometric route both run
over the one atom stream `atomStream row`. `phase_via_atoms` is the proven factorization;
`weilReadout` is the Weil route reading the SAME source. This is a dictionary, not an
analytic gate — it inhabits neither `SpectralZeroIdentity` nor global Weil positivity. -/
structure OCLSDWeilGeometricAdapter (A : FormalPhaseAlgebra) (W : WeilGeometricEvaluator) where
  phase_via_atoms : (row : PZGRow) → readPZGPhase A row = phaseOfAtoms A (atomStream row)
  weilReadout : PZGRow → W.Value

/-- Canonical adapter: the phase factorization is proven, and the Weil readout is the
Weil evaluator over the shared atom stream. -/
def mkAdapter (A : FormalPhaseAlgebra) (W : WeilGeometricEvaluator) :
    OCLSDWeilGeometricAdapter A W where
  phase_via_atoms := readPZGPhase_factors A
  weilReadout := fun row => weilOfAtoms W (atomStream row)

/-! ### Non-vacuity -/

/-- Atom concatenation is the stream image of register concatenation (both routes see
the same append structure). Propext-free. -/
theorem atomStream_append :
    ∀ xs ys : PZGRow,
      atomStream (pzgAppend xs ys) = atomStream xs ++ atomStream ys
  | PZGRow.nil, _ => rfl
  | PZGRow.cons p k xs, ys =>
      congrArg (List.cons (PrimeLogAtom.mk p k)) (atomStream_append xs ys)

/-- Concrete non-vacuity: the atom stream of `(2,1)(3,0)` is the two-atom list. -/
theorem atomStream_example :
    atomStream (PZGRow.cons 2 1 (PZGRow.cons 3 0 PZGRow.nil))
      = [{ prime := 2, fibIndex := 1 }, { prime := 3, fibIndex := 0 }] := rfl

end BEDC.Derived.RHRoute.OCLSDWeilGeometricAdapter
