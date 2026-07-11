import BEDC.Derived.RHRoute.OCLSDSpectral

/-
Prime-locked tick height (oracle conv_ff4ff126afd06e33 §3, anti-backward-fit).

The oracle flagged a backdoor: `RawGenerationStep` carries free `angle` / `logScale`
rows, so an adversary could feed `angle` = ζ zero heights and backward-fit the
spectrum. The fix is to require the per-tick height to be **prime-locked**: a function
of the prime register data (prime event, Zeckendorf bits, residual dimension) ONLY,
never of the free angle/logScale. Then `orbitHeight` — hence the eigenvalues of
`H_OCLSD` — cannot see the angle, so the spectrum is determined by prime arithmetic,
not tuned to the answer.

This module makes that a certificate: `PrimeLockedTickHeight` bundles a `TickHeightKit`
with a proof that its `tickHeight` factors through the prime-register projection, and
`primeLocked_angle_independent` derives that equal prime data ⟹ equal height
(angle-independence). All 0-axiom / propext-free.
-/

namespace BEDC.Derived.RHRoute.OCLSDPrimeLock

open BEDC.Derived.RHRoute.OCLSDSpectral
open BEDC.Derived.RHRoute.LocatedGenerationTower

/-- A prime-locked tick-height kit: a `TickHeightKit` whose `tickHeight` provably
factors through the prime-register data `(primeEvent, zeckBits, residualDim)`, never
the free `angle`/`logScale`. `locked` is the anti-backward-fit certificate. -/
structure PrimeLockedTickHeight (K : DynamicsTypes) where
  toKit : TickHeightKit K
  primeHeight : K.PrimeEvent → ZBits → UDim → toKit.Height
  locked : (raw : RawGenerationStep K) →
    toKit.tickHeight raw
      = primeHeight raw.primeEvent raw.zeckBits raw.residualDim

/-- Construct a prime-locked kit from any prime-register height function: the induced
`tickHeight` reads only the prime data, so `locked` holds by `rfl`. -/
def mkPrimeLocked {K : DynamicsTypes}
    (Ht : Type) (HEqk : EqKit Ht) (z : Ht) (ad : Ht → Ht → Ht)
    (ph : K.PrimeEvent → ZBits → UDim → Ht) : PrimeLockedTickHeight K where
  toKit :=
    { Height := Ht
      HEq := HEqk
      zero := z
      add := ad
      tickHeight := fun raw => ph raw.primeEvent raw.zeckBits raw.residualDim }
  primeHeight := ph
  locked := fun _ => rfl

/-- Anti-backward-fit: a prime-locked height is angle-independent — two ticks with the
same prime-register data have the same height, regardless of their `angle`/`logScale`.
Propext-free (`congrArg` + `Eq.trans`). -/
theorem primeLocked_angle_independent {K : DynamicsTypes}
    (P : PrimeLockedTickHeight K) (raw raw' : RawGenerationStep K)
    (h : (raw.primeEvent, raw.zeckBits, raw.residualDim)
       = (raw'.primeEvent, raw'.zeckBits, raw'.residualDim)) :
    P.toKit.tickHeight raw = P.toKit.tickHeight raw' :=
  (P.locked raw).trans
    ((congrArg (fun t => P.primeHeight t.1 t.2.1 t.2.2) h).trans
      (P.locked raw').symm)

/-! ### Non-vacuity -/

/-- A concrete prime-locked kit (height = residual dimension, `UDim`): certifies the
certificate is inhabited. -/
def toyPrimeLocked (K : DynamicsTypes) : PrimeLockedTickHeight K :=
  mkPrimeLocked UDim
    { Eqv := fun a b => PLift (a = b)
      refl := fun _ => ⟨rfl⟩
      symm := fun ⟨h⟩ => ⟨h.symm⟩
      trans := fun ⟨h1⟩ ⟨h2⟩ => ⟨h1.trans h2⟩ }
    UDim.zero UDim.add
    (fun _ _ rd => rd)

theorem toyPrimeLocked_locked (K : DynamicsTypes) (raw : RawGenerationStep K) :
    (toyPrimeLocked K).toKit.tickHeight raw = raw.residualDim := rfl

end BEDC.Derived.RHRoute.OCLSDPrimeLock
