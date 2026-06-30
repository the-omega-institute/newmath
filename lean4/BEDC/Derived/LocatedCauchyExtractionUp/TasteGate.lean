import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedCauchyExtractionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedCauchyExtractionUp : Type where
  | mk (Q L E W M R H C P N : BHist) : LocatedCauchyExtractionUp
  deriving DecidableEq

def locatedCauchyExtractionEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedCauchyExtractionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedCauchyExtractionEncodeBHist h

def locatedCauchyExtractionDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedCauchyExtractionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedCauchyExtractionDecodeBHist tail)

private theorem LocatedCauchyExtractionTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      locatedCauchyExtractionDecodeBHist (locatedCauchyExtractionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedCauchyExtractionFields : LocatedCauchyExtractionUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedCauchyExtractionUp.mk Q L E W M R H C P N => [Q, L, E, W, M, R, H, C, P, N]

def locatedCauchyExtractionToEventFlow : LocatedCauchyExtractionUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (locatedCauchyExtractionFields x).map locatedCauchyExtractionEncodeBHist

private def locatedCauchyExtractionEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatedCauchyExtractionEventAtDefault index rest

def locatedCauchyExtractionFromEventFlow
    (ef : EventFlow) : Option LocatedCauchyExtractionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocatedCauchyExtractionUp.mk
      (locatedCauchyExtractionDecodeBHist (locatedCauchyExtractionEventAtDefault 0 ef))
      (locatedCauchyExtractionDecodeBHist (locatedCauchyExtractionEventAtDefault 1 ef))
      (locatedCauchyExtractionDecodeBHist (locatedCauchyExtractionEventAtDefault 2 ef))
      (locatedCauchyExtractionDecodeBHist (locatedCauchyExtractionEventAtDefault 3 ef))
      (locatedCauchyExtractionDecodeBHist (locatedCauchyExtractionEventAtDefault 4 ef))
      (locatedCauchyExtractionDecodeBHist (locatedCauchyExtractionEventAtDefault 5 ef))
      (locatedCauchyExtractionDecodeBHist (locatedCauchyExtractionEventAtDefault 6 ef))
      (locatedCauchyExtractionDecodeBHist (locatedCauchyExtractionEventAtDefault 7 ef))
      (locatedCauchyExtractionDecodeBHist (locatedCauchyExtractionEventAtDefault 8 ef))
      (locatedCauchyExtractionDecodeBHist (locatedCauchyExtractionEventAtDefault 9 ef)))

private theorem LocatedCauchyExtractionTasteGate_single_carrier_alignment_fields :
    forall x y : LocatedCauchyExtractionUp,
      locatedCauchyExtractionFields x = locatedCauchyExtractionFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk Q1 L1 E1 W1 M1 R1 H1 C1 P1 N1 =>
      cases y with
      | mk Q2 L2 E2 W2 M2 R2 H2 C2 P2 N2 =>
          cases hfields
          rfl

theorem LocatedCauchyExtractionTasteGate_single_carrier_alignment :
    forall x : LocatedCauchyExtractionUp,
      locatedCauchyExtractionFromEventFlow (locatedCauchyExtractionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  intro token
  cases token with
  | mk Q L E W M R H C P N =>
      change
        some
          (LocatedCauchyExtractionUp.mk
            (locatedCauchyExtractionDecodeBHist (locatedCauchyExtractionEncodeBHist Q))
            (locatedCauchyExtractionDecodeBHist (locatedCauchyExtractionEncodeBHist L))
            (locatedCauchyExtractionDecodeBHist (locatedCauchyExtractionEncodeBHist E))
            (locatedCauchyExtractionDecodeBHist (locatedCauchyExtractionEncodeBHist W))
            (locatedCauchyExtractionDecodeBHist (locatedCauchyExtractionEncodeBHist M))
            (locatedCauchyExtractionDecodeBHist (locatedCauchyExtractionEncodeBHist R))
            (locatedCauchyExtractionDecodeBHist (locatedCauchyExtractionEncodeBHist H))
            (locatedCauchyExtractionDecodeBHist (locatedCauchyExtractionEncodeBHist C))
            (locatedCauchyExtractionDecodeBHist (locatedCauchyExtractionEncodeBHist P))
            (locatedCauchyExtractionDecodeBHist (locatedCauchyExtractionEncodeBHist N))) =
          some (LocatedCauchyExtractionUp.mk Q L E W M R H C P N)
      rw [LocatedCauchyExtractionTasteGate_single_carrier_alignment_decode Q,
        LocatedCauchyExtractionTasteGate_single_carrier_alignment_decode L,
        LocatedCauchyExtractionTasteGate_single_carrier_alignment_decode E,
        LocatedCauchyExtractionTasteGate_single_carrier_alignment_decode W,
        LocatedCauchyExtractionTasteGate_single_carrier_alignment_decode M,
        LocatedCauchyExtractionTasteGate_single_carrier_alignment_decode R,
        LocatedCauchyExtractionTasteGate_single_carrier_alignment_decode H,
        LocatedCauchyExtractionTasteGate_single_carrier_alignment_decode C,
        LocatedCauchyExtractionTasteGate_single_carrier_alignment_decode P,
        LocatedCauchyExtractionTasteGate_single_carrier_alignment_decode N]

private theorem LocatedCauchyExtractionTasteGate_single_carrier_alignment_injective
    {x y : LocatedCauchyExtractionUp} :
    locatedCauchyExtractionToEventFlow x = locatedCauchyExtractionToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedCauchyExtractionFromEventFlow (locatedCauchyExtractionToEventFlow x) =
        locatedCauchyExtractionFromEventFlow (locatedCauchyExtractionToEventFlow y) :=
    congrArg locatedCauchyExtractionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (LocatedCauchyExtractionTasteGate_single_carrier_alignment x).symm
      (Eq.trans hread (LocatedCauchyExtractionTasteGate_single_carrier_alignment y)))

instance locatedCauchyExtractionBHistCarrier : BHistCarrier LocatedCauchyExtractionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedCauchyExtractionToEventFlow
  fromEventFlow := locatedCauchyExtractionFromEventFlow

instance locatedCauchyExtractionChapterTasteGate :
    ChapterTasteGate LocatedCauchyExtractionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedCauchyExtractionFromEventFlow (locatedCauchyExtractionToEventFlow x) = some x
    exact LocatedCauchyExtractionTasteGate_single_carrier_alignment x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LocatedCauchyExtractionTasteGate_single_carrier_alignment_injective heq)

instance locatedCauchyExtractionFieldFaithful :
    FieldFaithful LocatedCauchyExtractionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := locatedCauchyExtractionFields
  field_faithful := LocatedCauchyExtractionTasteGate_single_carrier_alignment_fields

end BEDC.Derived.LocatedCauchyExtractionUp
