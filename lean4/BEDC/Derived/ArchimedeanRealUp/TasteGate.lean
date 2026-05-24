import BEDC.Derived.ArchimedeanRealUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ArchimedeanRealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ArchimedeanRealUp : Type where
  | mk :
      (realName ratBound dyadicBound streamWindow regseqHandoff boundLedger transport
        routes provenance localCert : BHist) →
        ArchimedeanRealUp
  deriving DecidableEq

def archimedeanRealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: archimedeanRealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: archimedeanRealEncodeBHist h

def archimedeanRealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (archimedeanRealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (archimedeanRealDecodeBHist tail)

private theorem archimedeanRealDecode_encode_bhist :
    ∀ h : BHist, archimedeanRealDecodeBHist (archimedeanRealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def archimedeanRealFields : ArchimedeanRealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ArchimedeanRealUp.mk realName ratBound dyadicBound streamWindow regseqHandoff
      boundLedger transport routes provenance localCert =>
      [realName, ratBound, dyadicBound, streamWindow, regseqHandoff, boundLedger, transport,
        routes, provenance, localCert]

def archimedeanRealToEventFlow : ArchimedeanRealUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (archimedeanRealFields x).map archimedeanRealEncodeBHist

def archimedeanRealFromEventFlow : EventFlow → Option ArchimedeanRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | realName :: ratBound :: dyadicBound :: streamWindow :: regseqHandoff :: boundLedger ::
      transport :: routes :: provenance :: localCert :: [] =>
      some
        (ArchimedeanRealUp.mk
          (archimedeanRealDecodeBHist realName)
          (archimedeanRealDecodeBHist ratBound)
          (archimedeanRealDecodeBHist dyadicBound)
          (archimedeanRealDecodeBHist streamWindow)
          (archimedeanRealDecodeBHist regseqHandoff)
          (archimedeanRealDecodeBHist boundLedger)
          (archimedeanRealDecodeBHist transport)
          (archimedeanRealDecodeBHist routes)
          (archimedeanRealDecodeBHist provenance)
          (archimedeanRealDecodeBHist localCert))
  | _ => none

private theorem archimedeanReal_round_trip :
    ∀ x : ArchimedeanRealUp,
      archimedeanRealFromEventFlow (archimedeanRealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk realName ratBound dyadicBound streamWindow regseqHandoff boundLedger transport routes
      provenance localCert =>
      change
        some
          (ArchimedeanRealUp.mk
            (archimedeanRealDecodeBHist (archimedeanRealEncodeBHist realName))
            (archimedeanRealDecodeBHist (archimedeanRealEncodeBHist ratBound))
            (archimedeanRealDecodeBHist (archimedeanRealEncodeBHist dyadicBound))
            (archimedeanRealDecodeBHist (archimedeanRealEncodeBHist streamWindow))
            (archimedeanRealDecodeBHist (archimedeanRealEncodeBHist regseqHandoff))
            (archimedeanRealDecodeBHist (archimedeanRealEncodeBHist boundLedger))
            (archimedeanRealDecodeBHist (archimedeanRealEncodeBHist transport))
            (archimedeanRealDecodeBHist (archimedeanRealEncodeBHist routes))
            (archimedeanRealDecodeBHist (archimedeanRealEncodeBHist provenance))
            (archimedeanRealDecodeBHist (archimedeanRealEncodeBHist localCert))) =
          some
            (ArchimedeanRealUp.mk realName ratBound dyadicBound streamWindow regseqHandoff
              boundLedger transport routes provenance localCert)
      rw [archimedeanRealDecode_encode_bhist realName,
        archimedeanRealDecode_encode_bhist ratBound,
        archimedeanRealDecode_encode_bhist dyadicBound,
        archimedeanRealDecode_encode_bhist streamWindow,
        archimedeanRealDecode_encode_bhist regseqHandoff,
        archimedeanRealDecode_encode_bhist boundLedger,
        archimedeanRealDecode_encode_bhist transport,
        archimedeanRealDecode_encode_bhist routes,
        archimedeanRealDecode_encode_bhist provenance,
        archimedeanRealDecode_encode_bhist localCert]

private theorem archimedeanRealToEventFlow_injective {x y : ArchimedeanRealUp} :
    archimedeanRealToEventFlow x = archimedeanRealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x = archimedeanRealFromEventFlow (archimedeanRealToEventFlow x) :=
        (archimedeanReal_round_trip x).symm
      _ = archimedeanRealFromEventFlow (archimedeanRealToEventFlow y) :=
        congrArg archimedeanRealFromEventFlow hxy
      _ = some y := archimedeanReal_round_trip y
  exact Option.some.inj optionEq

private theorem archimedeanReal_field_faithful :
    ∀ x y : ArchimedeanRealUp, archimedeanRealFields x = archimedeanRealFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk real1 rat1 dyadic1 stream1 regseq1 bound1 transport1 routes1 provenance1 cert1 =>
      cases y with
      | mk real2 rat2 dyadic2 stream2 regseq2 bound2 transport2 routes2 provenance2 cert2 =>
          injection h with hReal t1
          injection t1 with hRat t2
          injection t2 with hDyadic t3
          injection t3 with hStream t4
          injection t4 with hRegseq t5
          injection t5 with hBound t6
          injection t6 with hTransport t7
          injection t7 with hRoutes t8
          injection t8 with hProvenance t9
          injection t9 with hCert _
          cases hReal
          cases hRat
          cases hDyadic
          cases hStream
          cases hRegseq
          cases hBound
          cases hTransport
          cases hRoutes
          cases hProvenance
          cases hCert
          rfl

instance archimedeanRealBHistCarrier : BHistCarrier ArchimedeanRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := archimedeanRealToEventFlow
  fromEventFlow := archimedeanRealFromEventFlow

instance archimedeanRealChapterTasteGate :
    ChapterTasteGate ArchimedeanRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change archimedeanRealFromEventFlow (archimedeanRealToEventFlow x) = some x
    exact archimedeanReal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (archimedeanRealToEventFlow_injective heq)

instance archimedeanRealFieldFaithful : FieldFaithful ArchimedeanRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := archimedeanRealFields
  field_faithful := archimedeanReal_field_faithful

def taste_gate : ChapterTasteGate ArchimedeanRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  archimedeanRealChapterTasteGate

end BEDC.Derived.ArchimedeanRealUp
