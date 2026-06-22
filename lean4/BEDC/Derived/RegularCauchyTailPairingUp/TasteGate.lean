import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyTailPairingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyTailPairingUp : Type where
  | mk (streamLeft streamRight readbackLeft readbackRight dyadicLeft dyadicRight window
      handoff realSeal transports routes provenance name : BHist) : RegularCauchyTailPairingUp
  deriving DecidableEq

def regularCauchyTailPairingEncodeBHist : BHist → List BMark
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyTailPairingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyTailPairingEncodeBHist h

def regularCauchyTailPairingDecodeBHist : List BMark → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyTailPairingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyTailPairingDecodeBHist tail)

private theorem regularCauchyTailPairing_decode_encode :
    ∀ h : BHist,
      regularCauchyTailPairingDecodeBHist (regularCauchyTailPairingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyTailPairingFields : RegularCauchyTailPairingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyTailPairingUp.mk streamLeft streamRight readbackLeft readbackRight
      dyadicLeft dyadicRight window handoff realSeal transports routes provenance name =>
      [streamLeft, streamRight, readbackLeft, readbackRight, dyadicLeft, dyadicRight,
        window, handoff, realSeal, transports, routes, provenance, name]

def regularCauchyTailPairingToEventFlow : RegularCauchyTailPairingUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map regularCauchyTailPairingEncodeBHist (regularCauchyTailPairingFields x)

def regularCauchyTailPairingFromEventFlow : EventFlow → Option RegularCauchyTailPairingUp
  -- BEDC touchpoint anchor: BHist BMark
  | [streamLeft, streamRight, readbackLeft, readbackRight, dyadicLeft, dyadicRight,
      window, handoff, realSeal, transports, routes, provenance, name] =>
      some
        (RegularCauchyTailPairingUp.mk
          (regularCauchyTailPairingDecodeBHist streamLeft)
          (regularCauchyTailPairingDecodeBHist streamRight)
          (regularCauchyTailPairingDecodeBHist readbackLeft)
          (regularCauchyTailPairingDecodeBHist readbackRight)
          (regularCauchyTailPairingDecodeBHist dyadicLeft)
          (regularCauchyTailPairingDecodeBHist dyadicRight)
          (regularCauchyTailPairingDecodeBHist window)
          (regularCauchyTailPairingDecodeBHist handoff)
          (regularCauchyTailPairingDecodeBHist realSeal)
          (regularCauchyTailPairingDecodeBHist transports)
          (regularCauchyTailPairingDecodeBHist routes)
          (regularCauchyTailPairingDecodeBHist provenance)
          (regularCauchyTailPairingDecodeBHist name))
  | _ => none

private theorem regularCauchyTailPairing_round_trip :
    ∀ x : RegularCauchyTailPairingUp,
      regularCauchyTailPairingFromEventFlow
        (regularCauchyTailPairingToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk streamLeft streamRight readbackLeft readbackRight dyadicLeft dyadicRight window
      handoff realSeal transports routes provenance name =>
      change
        some
          (RegularCauchyTailPairingUp.mk
            (regularCauchyTailPairingDecodeBHist
              (regularCauchyTailPairingEncodeBHist streamLeft))
            (regularCauchyTailPairingDecodeBHist
              (regularCauchyTailPairingEncodeBHist streamRight))
            (regularCauchyTailPairingDecodeBHist
              (regularCauchyTailPairingEncodeBHist readbackLeft))
            (regularCauchyTailPairingDecodeBHist
              (regularCauchyTailPairingEncodeBHist readbackRight))
            (regularCauchyTailPairingDecodeBHist
              (regularCauchyTailPairingEncodeBHist dyadicLeft))
            (regularCauchyTailPairingDecodeBHist
              (regularCauchyTailPairingEncodeBHist dyadicRight))
            (regularCauchyTailPairingDecodeBHist
              (regularCauchyTailPairingEncodeBHist window))
            (regularCauchyTailPairingDecodeBHist
              (regularCauchyTailPairingEncodeBHist handoff))
            (regularCauchyTailPairingDecodeBHist
              (regularCauchyTailPairingEncodeBHist realSeal))
            (regularCauchyTailPairingDecodeBHist
              (regularCauchyTailPairingEncodeBHist transports))
            (regularCauchyTailPairingDecodeBHist
              (regularCauchyTailPairingEncodeBHist routes))
            (regularCauchyTailPairingDecodeBHist
              (regularCauchyTailPairingEncodeBHist provenance))
            (regularCauchyTailPairingDecodeBHist
              (regularCauchyTailPairingEncodeBHist name))) =
          some
            (RegularCauchyTailPairingUp.mk streamLeft streamRight readbackLeft
              readbackRight dyadicLeft dyadicRight window handoff realSeal transports routes
              provenance name)
      rw [regularCauchyTailPairing_decode_encode streamLeft,
        regularCauchyTailPairing_decode_encode streamRight,
        regularCauchyTailPairing_decode_encode readbackLeft,
        regularCauchyTailPairing_decode_encode readbackRight,
        regularCauchyTailPairing_decode_encode dyadicLeft,
        regularCauchyTailPairing_decode_encode dyadicRight,
        regularCauchyTailPairing_decode_encode window,
        regularCauchyTailPairing_decode_encode handoff,
        regularCauchyTailPairing_decode_encode realSeal,
        regularCauchyTailPairing_decode_encode transports,
        regularCauchyTailPairing_decode_encode routes,
        regularCauchyTailPairing_decode_encode provenance,
        regularCauchyTailPairing_decode_encode name]

private theorem regularCauchyTailPairingToEventFlow_injective
    {x y : RegularCauchyTailPairingUp} :
    regularCauchyTailPairingToEventFlow x = regularCauchyTailPairingToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyTailPairingFromEventFlow (regularCauchyTailPairingToEventFlow x) =
        regularCauchyTailPairingFromEventFlow (regularCauchyTailPairingToEventFlow y) :=
    congrArg regularCauchyTailPairingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyTailPairing_round_trip x).symm
      (Eq.trans hread (regularCauchyTailPairing_round_trip y)))

private theorem regularCauchyTailPairing_fields_faithful :
    ∀ x y : RegularCauchyTailPairingUp,
      regularCauchyTailPairingFields x = regularCauchyTailPairingFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk streamLeft₁ streamRight₁ readbackLeft₁ readbackRight₁ dyadicLeft₁ dyadicRight₁
      window₁ handoff₁ realSeal₁ transports₁ routes₁ provenance₁ name₁ =>
      cases y with
      | mk streamLeft₂ streamRight₂ readbackLeft₂ readbackRight₂ dyadicLeft₂ dyadicRight₂
          window₂ handoff₂ realSeal₂ transports₂ routes₂ provenance₂ name₂ =>
          cases hfields
          rfl

instance regularCauchyTailPairingBHistCarrier : BHistCarrier RegularCauchyTailPairingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyTailPairingToEventFlow
  fromEventFlow := regularCauchyTailPairingFromEventFlow

instance regularCauchyTailPairingChapterTasteGate :
    ChapterTasteGate RegularCauchyTailPairingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyTailPairingFromEventFlow (regularCauchyTailPairingToEventFlow x) =
        some x
    exact regularCauchyTailPairing_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyTailPairingToEventFlow_injective heq)

instance regularCauchyTailPairingFieldFaithful : FieldFaithful RegularCauchyTailPairingUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyTailPairingFields
  field_faithful := regularCauchyTailPairing_fields_faithful

instance regularCauchyTailPairingNontrivial : Nontrivial RegularCauchyTailPairingUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyTailPairingUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      RegularCauchyTailPairingUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegularCauchyTailPairingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyTailPairingChapterTasteGate

end BEDC.Derived.RegularCauchyTailPairingUp
