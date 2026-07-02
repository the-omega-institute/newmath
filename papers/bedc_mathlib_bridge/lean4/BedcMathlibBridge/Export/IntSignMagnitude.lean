import BedcMathlibBridge.Constructive.IntSignMagnitude

/-!
Export witness for the sign-magnitude presentation of BEDC `IntUp`.

The witness records the readback `BMark × BHist → Bool × Nat` of the
sign-magnitude carrier, the sign-bit/magnitude-length transports, the carrier
round-trip, and the faithfulness of `IntClassifierSpec` against `Bool × Nat`
equality. This is the presentation that keeps `+0` and `-0` distinct, so its
target is `Bool × Nat` rather than mathlib `Int`.
-/

namespace BedcMathlibBridge.Export.IntSignMagnitude

open BedcMathlibBridge.Constructive.IntSignMagnitude
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.Derived.IntUp

structure IntSignMagnitudeExportWitness where
  readback : BMark × BHist → Bool × Nat
  readback_apply : ∀ x : BMark × BHist, readback x = toBoolNat x
  ofBoolNat_carrier : ∀ bn : Bool × Nat,
    IntCarrier (BedcMathlibBridge.Constructive.IntSignMagnitude.ofBoolNat bn).1
      (BedcMathlibBridge.Constructive.IntSignMagnitude.ofBoolNat bn).2
  rightInv : ∀ bn : Bool × Nat, readback
    (BedcMathlibBridge.Constructive.IntSignMagnitude.ofBoolNat bn) = bn
  classifier_iff : ∀ {sx sy : BMark} {hx hy : BHist},
    IntCarrier sx hx → IntCarrier sy hy →
      (IntClassifierSpec (sx, hx) (sy, hy) ↔ readback (sx, hx) = readback (sy, hy))
  relQuotEquiv :
    BedcMathlibBridge.RelQuotEquiv
      {x : BMark × BHist // IntCarrier x.1 x.2}
      (fun a b => IntClassifierSpec a.val b.val)
      (Bool × Nat)

def intSignMagnitudeExport : IntSignMagnitudeExportWitness where
  readback := toBoolNat
  readback_apply := by
    intro x
    rfl
  ofBoolNat_carrier := BedcMathlibBridge.Constructive.IntSignMagnitude.ofBoolNat_carrier
  rightInv := BedcMathlibBridge.Constructive.IntSignMagnitude.rightInv
  classifier_iff := by
    intro sx sy hx hy cx cy
    exact BedcMathlibBridge.Constructive.IntSignMagnitude.relIff cx cy
  relQuotEquiv := BedcMathlibBridge.Constructive.IntSignMagnitude.intSignMagnitudeRelQuotEquiv

/-- Mathlib correspondence anchor: the BEDC sign-magnitude classifier equality
`IntClassifierSpec` is faithful against equality in `Bool × Nat` through the
`toBoolNat` readback. This is the Gate W value dependency for the row and
references both the BEDC anchor `IntClassifierSpec` and the mathlib target
`Bool`. -/
theorem intClassifierSpec_iff_boolNat_eq {sx sy : BMark} {hx hy : BHist}
    (cx : IntCarrier sx hx) (cy : IntCarrier sy hy) :
    IntClassifierSpec (sx, hx) (sy, hy) ↔
      (toBoolNat (sx, hx) : Bool × Nat) = toBoolNat (sy, hy) :=
  BedcMathlibBridge.Constructive.IntSignMagnitude.relIff cx cy

end BedcMathlibBridge.Export.IntSignMagnitude
