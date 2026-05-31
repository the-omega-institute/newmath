import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyProductAssociativityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyProductAssociativityUp : Type where
  | mk :
      (leftProduct rightProduct sourceX sourceY sourceZ modulusXY modulusYZ boundedXY boundedYZ
        dyadicLeft dyadicRight regularLeft regularRight sealLeft sealRight transport replay
        provenance localCert : BHist) →
      CauchyProductAssociativityUp
  deriving DecidableEq

def cauchyProductAssociativityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyProductAssociativityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyProductAssociativityEncodeBHist h

def cauchyProductAssociativityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyProductAssociativityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyProductAssociativityDecodeBHist tail)

theorem CauchyProductAssociativityTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cauchyProductAssociativityDecodeBHist
          (cauchyProductAssociativityEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyProductAssociativityFields : CauchyProductAssociativityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyProductAssociativityUp.mk leftProduct rightProduct sourceX sourceY sourceZ
      modulusXY modulusYZ boundedXY boundedYZ dyadicLeft dyadicRight regularLeft regularRight
      sealLeft sealRight transport replay provenance localCert =>
      [leftProduct, rightProduct, sourceX, sourceY, sourceZ, modulusXY, modulusYZ, boundedXY,
        boundedYZ, dyadicLeft, dyadicRight, regularLeft, regularRight, sealLeft, sealRight,
        transport, replay, provenance, localCert]

def cauchyProductAssociativityToEventFlow : CauchyProductAssociativityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      List.map cauchyProductAssociativityEncodeBHist
        (cauchyProductAssociativityFields x)

private def cauchyProductAssociativityEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyProductAssociativityEventAtDefault index rest

def cauchyProductAssociativityFromEventFlow :
    EventFlow → Option CauchyProductAssociativityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (CauchyProductAssociativityUp.mk
        (cauchyProductAssociativityDecodeBHist
          (cauchyProductAssociativityEventAtDefault 0 ef))
        (cauchyProductAssociativityDecodeBHist
          (cauchyProductAssociativityEventAtDefault 1 ef))
        (cauchyProductAssociativityDecodeBHist
          (cauchyProductAssociativityEventAtDefault 2 ef))
        (cauchyProductAssociativityDecodeBHist
          (cauchyProductAssociativityEventAtDefault 3 ef))
        (cauchyProductAssociativityDecodeBHist
          (cauchyProductAssociativityEventAtDefault 4 ef))
        (cauchyProductAssociativityDecodeBHist
          (cauchyProductAssociativityEventAtDefault 5 ef))
        (cauchyProductAssociativityDecodeBHist
          (cauchyProductAssociativityEventAtDefault 6 ef))
        (cauchyProductAssociativityDecodeBHist
          (cauchyProductAssociativityEventAtDefault 7 ef))
        (cauchyProductAssociativityDecodeBHist
          (cauchyProductAssociativityEventAtDefault 8 ef))
        (cauchyProductAssociativityDecodeBHist
          (cauchyProductAssociativityEventAtDefault 9 ef))
        (cauchyProductAssociativityDecodeBHist
          (cauchyProductAssociativityEventAtDefault 10 ef))
        (cauchyProductAssociativityDecodeBHist
          (cauchyProductAssociativityEventAtDefault 11 ef))
        (cauchyProductAssociativityDecodeBHist
          (cauchyProductAssociativityEventAtDefault 12 ef))
        (cauchyProductAssociativityDecodeBHist
          (cauchyProductAssociativityEventAtDefault 13 ef))
        (cauchyProductAssociativityDecodeBHist
          (cauchyProductAssociativityEventAtDefault 14 ef))
        (cauchyProductAssociativityDecodeBHist
          (cauchyProductAssociativityEventAtDefault 15 ef))
        (cauchyProductAssociativityDecodeBHist
          (cauchyProductAssociativityEventAtDefault 16 ef))
        (cauchyProductAssociativityDecodeBHist
          (cauchyProductAssociativityEventAtDefault 17 ef))
        (cauchyProductAssociativityDecodeBHist
          (cauchyProductAssociativityEventAtDefault 18 ef)))

private theorem cauchyProductAssociativity_round_trip :
    ∀ x : CauchyProductAssociativityUp,
      cauchyProductAssociativityFromEventFlow
          (cauchyProductAssociativityToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk leftProduct rightProduct sourceX sourceY sourceZ modulusXY modulusYZ boundedXY boundedYZ
      dyadicLeft dyadicRight regularLeft regularRight sealLeft sealRight transport replay
      provenance localCert =>
      change
        some
          (CauchyProductAssociativityUp.mk
            (cauchyProductAssociativityDecodeBHist
              (cauchyProductAssociativityEncodeBHist leftProduct))
            (cauchyProductAssociativityDecodeBHist
              (cauchyProductAssociativityEncodeBHist rightProduct))
            (cauchyProductAssociativityDecodeBHist
              (cauchyProductAssociativityEncodeBHist sourceX))
            (cauchyProductAssociativityDecodeBHist
              (cauchyProductAssociativityEncodeBHist sourceY))
            (cauchyProductAssociativityDecodeBHist
              (cauchyProductAssociativityEncodeBHist sourceZ))
            (cauchyProductAssociativityDecodeBHist
              (cauchyProductAssociativityEncodeBHist modulusXY))
            (cauchyProductAssociativityDecodeBHist
              (cauchyProductAssociativityEncodeBHist modulusYZ))
            (cauchyProductAssociativityDecodeBHist
              (cauchyProductAssociativityEncodeBHist boundedXY))
            (cauchyProductAssociativityDecodeBHist
              (cauchyProductAssociativityEncodeBHist boundedYZ))
            (cauchyProductAssociativityDecodeBHist
              (cauchyProductAssociativityEncodeBHist dyadicLeft))
            (cauchyProductAssociativityDecodeBHist
              (cauchyProductAssociativityEncodeBHist dyadicRight))
            (cauchyProductAssociativityDecodeBHist
              (cauchyProductAssociativityEncodeBHist regularLeft))
            (cauchyProductAssociativityDecodeBHist
              (cauchyProductAssociativityEncodeBHist regularRight))
            (cauchyProductAssociativityDecodeBHist
              (cauchyProductAssociativityEncodeBHist sealLeft))
            (cauchyProductAssociativityDecodeBHist
              (cauchyProductAssociativityEncodeBHist sealRight))
            (cauchyProductAssociativityDecodeBHist
              (cauchyProductAssociativityEncodeBHist transport))
            (cauchyProductAssociativityDecodeBHist
              (cauchyProductAssociativityEncodeBHist replay))
            (cauchyProductAssociativityDecodeBHist
              (cauchyProductAssociativityEncodeBHist provenance))
            (cauchyProductAssociativityDecodeBHist
              (cauchyProductAssociativityEncodeBHist localCert))) =
          some
            (CauchyProductAssociativityUp.mk leftProduct rightProduct sourceX sourceY sourceZ
              modulusXY modulusYZ boundedXY boundedYZ dyadicLeft dyadicRight regularLeft
              regularRight sealLeft sealRight transport replay provenance localCert)
      rw [CauchyProductAssociativityTasteGate_single_carrier_alignment_decode_encode
          leftProduct,
        CauchyProductAssociativityTasteGate_single_carrier_alignment_decode_encode
          rightProduct,
        CauchyProductAssociativityTasteGate_single_carrier_alignment_decode_encode sourceX,
        CauchyProductAssociativityTasteGate_single_carrier_alignment_decode_encode sourceY,
        CauchyProductAssociativityTasteGate_single_carrier_alignment_decode_encode sourceZ,
        CauchyProductAssociativityTasteGate_single_carrier_alignment_decode_encode modulusXY,
        CauchyProductAssociativityTasteGate_single_carrier_alignment_decode_encode modulusYZ,
        CauchyProductAssociativityTasteGate_single_carrier_alignment_decode_encode boundedXY,
        CauchyProductAssociativityTasteGate_single_carrier_alignment_decode_encode boundedYZ,
        CauchyProductAssociativityTasteGate_single_carrier_alignment_decode_encode dyadicLeft,
        CauchyProductAssociativityTasteGate_single_carrier_alignment_decode_encode dyadicRight,
        CauchyProductAssociativityTasteGate_single_carrier_alignment_decode_encode regularLeft,
        CauchyProductAssociativityTasteGate_single_carrier_alignment_decode_encode regularRight,
        CauchyProductAssociativityTasteGate_single_carrier_alignment_decode_encode sealLeft,
        CauchyProductAssociativityTasteGate_single_carrier_alignment_decode_encode sealRight,
        CauchyProductAssociativityTasteGate_single_carrier_alignment_decode_encode transport,
        CauchyProductAssociativityTasteGate_single_carrier_alignment_decode_encode replay,
        CauchyProductAssociativityTasteGate_single_carrier_alignment_decode_encode provenance,
        CauchyProductAssociativityTasteGate_single_carrier_alignment_decode_encode localCert]

private theorem cauchyProductAssociativityToEventFlow_injective
    {x y : CauchyProductAssociativityUp} :
    cauchyProductAssociativityToEventFlow x =
      cauchyProductAssociativityToEventFlow y →
    x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyProductAssociativityFromEventFlow (cauchyProductAssociativityToEventFlow x) =
        cauchyProductAssociativityFromEventFlow (cauchyProductAssociativityToEventFlow y) :=
    congrArg cauchyProductAssociativityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyProductAssociativity_round_trip x).symm
      (Eq.trans hread (cauchyProductAssociativity_round_trip y)))

instance cauchyProductAssociativityBHistCarrier :
    BHistCarrier CauchyProductAssociativityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyProductAssociativityToEventFlow
  fromEventFlow := cauchyProductAssociativityFromEventFlow

instance cauchyProductAssociativityChapterTasteGate :
    ChapterTasteGate CauchyProductAssociativityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyProductAssociativityFromEventFlow
          (cauchyProductAssociativityToEventFlow x) =
        some x
    exact cauchyProductAssociativity_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyProductAssociativityToEventFlow_injective heq)

theorem CauchyProductAssociativityTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        cauchyProductAssociativityDecodeBHist
            (cauchyProductAssociativityEncodeBHist h) =
          h) ∧
      Nonempty (BHistCarrier CauchyProductAssociativityUp) ∧
      Nonempty (ChapterTasteGate CauchyProductAssociativityUp) ∧
      cauchyProductAssociativityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact CauchyProductAssociativityTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact Nonempty.intro cauchyProductAssociativityBHistCarrier
    · constructor
      · exact Nonempty.intro cauchyProductAssociativityChapterTasteGate
      · rfl

end BEDC.Derived.CauchyProductAssociativityUp
