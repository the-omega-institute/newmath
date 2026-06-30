import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.QRDecompositionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive QRDecompositionUp : Type where
  | mk (A Q0 R G T H C P N : BHist) : QRDecompositionUp
  deriving DecidableEq

def qrDecompositionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: qrDecompositionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: qrDecompositionEncodeBHist h

def qrDecompositionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (qrDecompositionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (qrDecompositionDecodeBHist tail)

private theorem qrDecompositionDecodeEncode :
    ∀ h : BHist, qrDecompositionDecodeBHist (qrDecompositionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def qrDecompositionFields : QRDecompositionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | QRDecompositionUp.mk A Q0 R G T H C P N => [A, Q0, R, G, T, H, C, P, N]

def qrDecompositionToEventFlow : QRDecompositionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (qrDecompositionFields x).map qrDecompositionEncodeBHist

def qrDecompositionFromEventFlow : EventFlow → Option QRDecompositionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun eventFlow =>
    match eventFlow with
    | [] => none
    | _ :: [] => none
    | _ :: _ :: [] => none
    | _ :: _ :: _ :: [] => none
    | _ :: _ :: _ :: _ :: [] => none
    | _ :: _ :: _ :: _ :: _ :: [] => none
    | _ :: _ :: _ :: _ :: _ :: _ :: [] => none
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
    | A :: Q0 :: R :: G :: T :: H :: C :: P :: N :: [] =>
        some
          (QRDecompositionUp.mk
            (qrDecompositionDecodeBHist A)
            (qrDecompositionDecodeBHist Q0)
            (qrDecompositionDecodeBHist R)
            (qrDecompositionDecodeBHist G)
            (qrDecompositionDecodeBHist T)
            (qrDecompositionDecodeBHist H)
            (qrDecompositionDecodeBHist C)
            (qrDecompositionDecodeBHist P)
            (qrDecompositionDecodeBHist N))
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ => none

private theorem qrDecompositionRoundTrip :
    ∀ x : QRDecompositionUp,
      qrDecompositionFromEventFlow (qrDecompositionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A Q0 R G T H C P N =>
      change
        some
            (QRDecompositionUp.mk
              (qrDecompositionDecodeBHist (qrDecompositionEncodeBHist A))
              (qrDecompositionDecodeBHist (qrDecompositionEncodeBHist Q0))
              (qrDecompositionDecodeBHist (qrDecompositionEncodeBHist R))
              (qrDecompositionDecodeBHist (qrDecompositionEncodeBHist G))
              (qrDecompositionDecodeBHist (qrDecompositionEncodeBHist T))
              (qrDecompositionDecodeBHist (qrDecompositionEncodeBHist H))
              (qrDecompositionDecodeBHist (qrDecompositionEncodeBHist C))
              (qrDecompositionDecodeBHist (qrDecompositionEncodeBHist P))
              (qrDecompositionDecodeBHist (qrDecompositionEncodeBHist N))) =
          some (QRDecompositionUp.mk A Q0 R G T H C P N)
      rw [qrDecompositionDecodeEncode A, qrDecompositionDecodeEncode Q0,
        qrDecompositionDecodeEncode R, qrDecompositionDecodeEncode G,
        qrDecompositionDecodeEncode T, qrDecompositionDecodeEncode H,
        qrDecompositionDecodeEncode C, qrDecompositionDecodeEncode P,
        qrDecompositionDecodeEncode N]

private theorem qrDecompositionToEventFlow_injective {x y : QRDecompositionUp} :
    qrDecompositionToEventFlow x = qrDecompositionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      qrDecompositionFromEventFlow (qrDecompositionToEventFlow x) =
        qrDecompositionFromEventFlow (qrDecompositionToEventFlow y) :=
    congrArg qrDecompositionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (qrDecompositionRoundTrip x).symm
      (Eq.trans hread (qrDecompositionRoundTrip y)))

def qrDecompositionCarrier : BHistCarrier QRDecompositionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := qrDecompositionToEventFlow
  fromEventFlow := qrDecompositionFromEventFlow

instance qrDecompositionBHistCarrier : BHistCarrier QRDecompositionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  qrDecompositionCarrier

def qrDecompositionGate : @ChapterTasteGate QRDecompositionUp qrDecompositionCarrier where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change qrDecompositionFromEventFlow (qrDecompositionToEventFlow x) = some x
    exact qrDecompositionRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (qrDecompositionToEventFlow_injective heq)

instance qrDecompositionChapterTasteGate : ChapterTasteGate QRDecompositionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  qrDecompositionGate

theorem QRDecompositionTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier QRDecompositionUp) ∧
      Nonempty (ChapterTasteGate QRDecompositionUp) ∧
        qrDecompositionFields
            (QRDecompositionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
          [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
            BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact ⟨⟨qrDecompositionCarrier⟩, ⟨qrDecompositionGate⟩, rfl⟩

end BEDC.Derived.QRDecompositionUp
