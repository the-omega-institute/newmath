import BEDC.Derived.IntUp
import BEDC.Derived.IntUp.Arithmetic
import BEDC.Derived.NatUp
import BEDC.FKernel.ExternalBinary
import BEDC.FKernel.Unary
import BedcMathlibBridge.Core.RelQuotEquiv

/-!
Sign-magnitude presentation of BEDC `IntUp` bridged to `Bool × Nat`.

`BEDC.Derived.IntUp` carries two independent presentations of the signed
integers:

* the *difference* presentation `IntPairCarrier p n` reading `p - n`, whose
  equality `IntPairClassifier` collapses `+0` and `-0`; this presentation is
  already bridged to mathlib `Int` as `CInt ≃+* Int` in
  `BedcMathlibBridge.Constructive.Int`.
* the *sign-magnitude* presentation `IntCarrier sign magnitude`, a raw
  `(BMark × BHist)` datum whose equality `IntClassifierSpec` requires both
  `msame` on the sign mark and `hsame` on the unary magnitude history. By
  `IntClassifierSpec_cross_sign_exclusion` this relation keeps `+0` and `-0`
  distinct, so it is strictly finer than integer equality.

This file bridges the sign-magnitude presentation. Its faithful finite readback
is therefore not `Int` but `Bool × Nat` (a sign bit paired with the magnitude
length): the negative-sign mark `b1` becomes `true`, the nonnegative mark `b0`
becomes `false`, and the unary magnitude history reads back through
`bwordLength`. Because `msame`/`hsame` are `Eq` and the standard unary bridge
makes `hsame` on unary histories equivalent to equal `bwordLength`, the readback
is a genuine bijection on carriers: `IntClassifierSpec` holds exactly when the
`Bool × Nat` readbacks coincide. Everything here is a thin, 0-axiom transport;
no new arithmetic is introduced.
-/

namespace BedcMathlibBridge.Constructive.IntSignMagnitude

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.IntUp

/-- The sign bit of a BEDC sign-magnitude datum: `true` for the negative mark
`b1`, `false` for the nonnegative mark `b0`. -/
def signBit (s : BMark) : Bool :=
  match s with
  | BMark.b0 => false
  | BMark.b1 => true

/-- Recover a sign mark from a sign bit. -/
def markOfBit (b : Bool) : BMark :=
  if b then BMark.b1 else BMark.b0

theorem markOfBit_signBit (s : BMark) : markOfBit (signBit s) = s := by
  cases s with
  | b0 => rfl
  | b1 => rfl

theorem signBit_markOfBit (b : Bool) : signBit (markOfBit b) = b := by
  cases b with
  | false => rfl
  | true => rfl

/-- Sign mark equality is decided by the sign bit. -/
theorem signBit_eq_iff {s t : BMark} : signBit s = signBit t ↔ s = t := by
  constructor
  · intro h
    have := congrArg markOfBit h
    rw [markOfBit_signBit, markOfBit_signBit] at this
    exact this
  · intro h
    exact congrArg signBit h

/-- Readback of a sign-magnitude datum into `Bool × Nat`. -/
def toBoolNat (x : BMark × BHist) : Bool × Nat :=
  (signBit x.1, bwordLength x.2)

/-- Build a canonical sign-magnitude datum from `Bool × Nat` data, using the
unary history of the magnitude. -/
def ofBoolNat (bn : Bool × Nat) : BMark × BHist :=
  (markOfBit bn.1, natToUnary bn.2)

theorem ofBoolNat_carrier (bn : Bool × Nat) :
    IntCarrier (ofBoolNat bn).1 (ofBoolNat bn).2 := by
  refine ⟨?_, natToUnary_unary bn.2⟩
  show markOfBit bn.1 = BMark.b0 ∨ markOfBit bn.1 = BMark.b1
  cases bn.1 with
  | false => exact Or.inl rfl
  | true => exact Or.inr rfl

theorem rightInv (bn : Bool × Nat) : toBoolNat (ofBoolNat bn) = bn := by
  cases bn with
  | mk b n =>
      unfold toBoolNat ofBoolNat
      apply Prod.ext
      · exact signBit_markOfBit b
      · exact natToUnary_length n

/-- Faithfulness: the sign-magnitude classifier equality holds exactly when the
`Bool × Nat` readbacks coincide. Both directions use only the standard unary
length bridge for the magnitude; the sign part is `msame = Eq` read through the
sign bit. -/
theorem relIff {sx sy : BMark} {hx hy : BHist}
    (cx : IntCarrier sx hx) (cy : IntCarrier sy hy) :
    IntClassifierSpec (sx, hx) (sy, hy) ↔
      toBoolNat (sx, hx) = toBoolNat (sy, hy) := by
  have bridge := BEDC.Derived.NatUp.NatUp_unary_standard_bridge
  rcases bridge with ⟨_emptyLength, _succLength, _noZero, sameIff, _contAdd⟩
  constructor
  · intro classified
    have sameSign : sx = sy := classified.right.right.left
    have sameMag : hsame hx hy := classified.right.right.right
    have lenEq : bwordLength hx = bwordLength hy :=
      (sameIff cx.right cy.right).mp sameMag
    unfold toBoolNat
    apply Prod.ext
    · exact congrArg signBit sameSign
    · exact lenEq
  · intro readbackEq
    have signEq : signBit sx = signBit sy := congrArg Prod.fst readbackEq
    have lenEq : bwordLength hx = bwordLength hy := congrArg Prod.snd readbackEq
    refine ⟨cx, cy, ?_, ?_⟩
    · exact signBit_eq_iff.mp signEq
    · exact (sameIff cx.right cy.right).mpr lenEq

theorem leftInvRel {sx : BMark} {hx : BHist} (carrier : IntCarrier sx hx) :
    IntClassifierSpec (ofBoolNat (toBoolNat (sx, hx))) (sx, hx) := by
  have sourceCarrier := ofBoolNat_carrier (toBoolNat (sx, hx))
  refine (relIff sourceCarrier carrier).mpr ?_
  exact rightInv (toBoolNat (sx, hx))

/-- The sign-magnitude carrier subtype, quotiented by `IntClassifierSpec`,
corresponds to `Bool × Nat`. -/
def intSignMagnitudeRelQuotEquiv :
    BedcMathlibBridge.RelQuotEquiv
      {x : BMark × BHist // IntCarrier x.1 x.2}
      (fun a b => IntClassifierSpec a.val b.val)
      (Bool × Nat) where
  toM := fun a => toBoolNat a.val
  ofM := fun bn => ⟨ofBoolNat bn, ofBoolNat_carrier bn⟩
  leftInvRel := by
    intro a
    rcases a with ⟨⟨sx, hx⟩, carrier⟩
    exact leftInvRel carrier
  rightInv := by
    intro bn
    exact rightInv bn
  relIff := by
    intro a b
    rcases a with ⟨⟨sx, hx⟩, carrierA⟩
    rcases b with ⟨⟨sy, hy⟩, carrierB⟩
    exact relIff carrierA carrierB

end BedcMathlibBridge.Constructive.IntSignMagnitude
