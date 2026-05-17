import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.StandardBridgeAuditPacketUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive StandardBridgeAuditPacketUp : Type where
  | mk : (N T E D R U P L H C Q : BHist) → StandardBridgeAuditPacketUp
  deriving DecidableEq

private def standardBridgeAuditPacketEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: standardBridgeAuditPacketEncodeBHist h
  | BHist.e1 h => BMark.b1 :: standardBridgeAuditPacketEncodeBHist h

private def standardBridgeAuditPacketDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (standardBridgeAuditPacketDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (standardBridgeAuditPacketDecodeBHist tail)

private theorem standardBridgeAuditPacket_decode_encode_bhist :
    ∀ h : BHist,
      standardBridgeAuditPacketDecodeBHist
        (standardBridgeAuditPacketEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def standardBridgeAuditPacketToEventFlow :
    StandardBridgeAuditPacketUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | StandardBridgeAuditPacketUp.mk N T E D R U P L H C Q =>
      [standardBridgeAuditPacketEncodeBHist N,
        standardBridgeAuditPacketEncodeBHist T,
        standardBridgeAuditPacketEncodeBHist E,
        standardBridgeAuditPacketEncodeBHist D,
        standardBridgeAuditPacketEncodeBHist R,
        standardBridgeAuditPacketEncodeBHist U,
        standardBridgeAuditPacketEncodeBHist P,
        standardBridgeAuditPacketEncodeBHist L,
        standardBridgeAuditPacketEncodeBHist H,
        standardBridgeAuditPacketEncodeBHist C,
        standardBridgeAuditPacketEncodeBHist Q]

private def standardBridgeAuditPacketFromEventFlow :
    EventFlow → Option StandardBridgeAuditPacketUp
  -- BEDC touchpoint anchor: BHist BMark
  | N :: T :: E :: D :: R :: U :: P :: L :: H :: C :: Q :: [] =>
      some
        (StandardBridgeAuditPacketUp.mk
          (standardBridgeAuditPacketDecodeBHist N)
          (standardBridgeAuditPacketDecodeBHist T)
          (standardBridgeAuditPacketDecodeBHist E)
          (standardBridgeAuditPacketDecodeBHist D)
          (standardBridgeAuditPacketDecodeBHist R)
          (standardBridgeAuditPacketDecodeBHist U)
          (standardBridgeAuditPacketDecodeBHist P)
          (standardBridgeAuditPacketDecodeBHist L)
          (standardBridgeAuditPacketDecodeBHist H)
          (standardBridgeAuditPacketDecodeBHist C)
          (standardBridgeAuditPacketDecodeBHist Q))
  | _ => none

private theorem standardBridgeAuditPacket_round_trip :
    ∀ x : StandardBridgeAuditPacketUp,
      standardBridgeAuditPacketFromEventFlow
        (standardBridgeAuditPacketToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk N T E D R U P L H C Q =>
      change
        some
          (StandardBridgeAuditPacketUp.mk
            (standardBridgeAuditPacketDecodeBHist
              (standardBridgeAuditPacketEncodeBHist N))
            (standardBridgeAuditPacketDecodeBHist
              (standardBridgeAuditPacketEncodeBHist T))
            (standardBridgeAuditPacketDecodeBHist
              (standardBridgeAuditPacketEncodeBHist E))
            (standardBridgeAuditPacketDecodeBHist
              (standardBridgeAuditPacketEncodeBHist D))
            (standardBridgeAuditPacketDecodeBHist
              (standardBridgeAuditPacketEncodeBHist R))
            (standardBridgeAuditPacketDecodeBHist
              (standardBridgeAuditPacketEncodeBHist U))
            (standardBridgeAuditPacketDecodeBHist
              (standardBridgeAuditPacketEncodeBHist P))
            (standardBridgeAuditPacketDecodeBHist
              (standardBridgeAuditPacketEncodeBHist L))
            (standardBridgeAuditPacketDecodeBHist
              (standardBridgeAuditPacketEncodeBHist H))
            (standardBridgeAuditPacketDecodeBHist
              (standardBridgeAuditPacketEncodeBHist C))
            (standardBridgeAuditPacketDecodeBHist
              (standardBridgeAuditPacketEncodeBHist Q))) =
          some (StandardBridgeAuditPacketUp.mk N T E D R U P L H C Q)
      rw [standardBridgeAuditPacket_decode_encode_bhist N,
        standardBridgeAuditPacket_decode_encode_bhist T,
        standardBridgeAuditPacket_decode_encode_bhist E,
        standardBridgeAuditPacket_decode_encode_bhist D,
        standardBridgeAuditPacket_decode_encode_bhist R,
        standardBridgeAuditPacket_decode_encode_bhist U,
        standardBridgeAuditPacket_decode_encode_bhist P,
        standardBridgeAuditPacket_decode_encode_bhist L,
        standardBridgeAuditPacket_decode_encode_bhist H,
        standardBridgeAuditPacket_decode_encode_bhist C,
        standardBridgeAuditPacket_decode_encode_bhist Q]

private theorem standardBridgeAuditPacketToEventFlow_injective
    {x y : StandardBridgeAuditPacketUp} :
    standardBridgeAuditPacketToEventFlow x =
      standardBridgeAuditPacketToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      standardBridgeAuditPacketFromEventFlow
          (standardBridgeAuditPacketToEventFlow x) =
        standardBridgeAuditPacketFromEventFlow
          (standardBridgeAuditPacketToEventFlow y) :=
    congrArg standardBridgeAuditPacketFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (standardBridgeAuditPacket_round_trip x).symm
      (Eq.trans hread (standardBridgeAuditPacket_round_trip y)))

instance standardBridgeAuditPacketBHistCarrier :
    BHistCarrier StandardBridgeAuditPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := standardBridgeAuditPacketToEventFlow
  fromEventFlow := standardBridgeAuditPacketFromEventFlow

instance standardBridgeAuditPacketChapterTasteGate :
    ChapterTasteGate StandardBridgeAuditPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      standardBridgeAuditPacketFromEventFlow
        (standardBridgeAuditPacketToEventFlow x) = some x
    exact standardBridgeAuditPacket_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (standardBridgeAuditPacketToEventFlow_injective heq)

instance standardBridgeAuditPacketFieldFaithful :
    FieldFaithful StandardBridgeAuditPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields
    | StandardBridgeAuditPacketUp.mk N T E D R U P L H C Q =>
        [N, T, E, D, R, U, P, L, H, C, Q]
  field_faithful := by
    intro x y hfields
    cases x with
    | mk N T E D R U P L H C Q =>
        cases y with
        | mk N' T' E' D' R' U' P' L' H' C' Q' =>
            cases hfields
            rfl

instance standardBridgeAuditPacketNontrivial :
    Nontrivial StandardBridgeAuditPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨StandardBridgeAuditPacketUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      StandardBridgeAuditPacketUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate StandardBridgeAuditPacketUp :=
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  standardBridgeAuditPacketChapterTasteGate

def StandardBridgeAuditPacketUp_taste_gate_obligations :
    ChapterTasteGate StandardBridgeAuditPacketUp := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact taste_gate

end BEDC.Derived.StandardBridgeAuditPacketUp
