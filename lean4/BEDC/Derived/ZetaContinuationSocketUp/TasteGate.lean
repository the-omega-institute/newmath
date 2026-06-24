import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ZetaContinuationSocketUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ZetaContinuationSocketUp : Type where
  | mk (B E A P F T G H C N : BHist) : ZetaContinuationSocketUp
  deriving DecidableEq

def zetaContinuationSocketEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: zetaContinuationSocketEncodeBHist h
  | BHist.e1 h => BMark.b1 :: zetaContinuationSocketEncodeBHist h

def zetaContinuationSocketDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (zetaContinuationSocketDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (zetaContinuationSocketDecodeBHist tail)

private theorem zetaContinuationSocket_decode_encode :
    forall h : BHist,
      zetaContinuationSocketDecodeBHist (zetaContinuationSocketEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def zetaContinuationSocketFields : ZetaContinuationSocketUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ZetaContinuationSocketUp.mk B E A P F T G H C N => [B, E, A, P, F, T, G, H, C, N]

def zetaContinuationSocketToEventFlow : ZetaContinuationSocketUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map zetaContinuationSocketEncodeBHist (zetaContinuationSocketFields x)

private def zetaContinuationSocketEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => zetaContinuationSocketEventAt index rest

def zetaContinuationSocketFromEventFlow : EventFlow -> Option ZetaContinuationSocketUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (ZetaContinuationSocketUp.mk
          (zetaContinuationSocketDecodeBHist (zetaContinuationSocketEventAt 0 ef))
          (zetaContinuationSocketDecodeBHist (zetaContinuationSocketEventAt 1 ef))
          (zetaContinuationSocketDecodeBHist (zetaContinuationSocketEventAt 2 ef))
          (zetaContinuationSocketDecodeBHist (zetaContinuationSocketEventAt 3 ef))
          (zetaContinuationSocketDecodeBHist (zetaContinuationSocketEventAt 4 ef))
          (zetaContinuationSocketDecodeBHist (zetaContinuationSocketEventAt 5 ef))
          (zetaContinuationSocketDecodeBHist (zetaContinuationSocketEventAt 6 ef))
          (zetaContinuationSocketDecodeBHist (zetaContinuationSocketEventAt 7 ef))
          (zetaContinuationSocketDecodeBHist (zetaContinuationSocketEventAt 8 ef))
          (zetaContinuationSocketDecodeBHist (zetaContinuationSocketEventAt 9 ef)))

private theorem zetaContinuationSocket_round_trip :
    forall x : ZetaContinuationSocketUp,
      zetaContinuationSocketFromEventFlow (zetaContinuationSocketToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B E A P F T G H C N =>
      change
        some
            (ZetaContinuationSocketUp.mk
              (zetaContinuationSocketDecodeBHist (zetaContinuationSocketEncodeBHist B))
              (zetaContinuationSocketDecodeBHist (zetaContinuationSocketEncodeBHist E))
              (zetaContinuationSocketDecodeBHist (zetaContinuationSocketEncodeBHist A))
              (zetaContinuationSocketDecodeBHist (zetaContinuationSocketEncodeBHist P))
              (zetaContinuationSocketDecodeBHist (zetaContinuationSocketEncodeBHist F))
              (zetaContinuationSocketDecodeBHist (zetaContinuationSocketEncodeBHist T))
              (zetaContinuationSocketDecodeBHist (zetaContinuationSocketEncodeBHist G))
              (zetaContinuationSocketDecodeBHist (zetaContinuationSocketEncodeBHist H))
              (zetaContinuationSocketDecodeBHist (zetaContinuationSocketEncodeBHist C))
              (zetaContinuationSocketDecodeBHist (zetaContinuationSocketEncodeBHist N))) =
          some (ZetaContinuationSocketUp.mk B E A P F T G H C N)
      rw [zetaContinuationSocket_decode_encode B, zetaContinuationSocket_decode_encode E,
        zetaContinuationSocket_decode_encode A, zetaContinuationSocket_decode_encode P,
        zetaContinuationSocket_decode_encode F, zetaContinuationSocket_decode_encode T,
        zetaContinuationSocket_decode_encode G, zetaContinuationSocket_decode_encode H,
        zetaContinuationSocket_decode_encode C, zetaContinuationSocket_decode_encode N]

private theorem zetaContinuationSocketToEventFlow_injective
    {x y : ZetaContinuationSocketUp} :
    zetaContinuationSocketToEventFlow x = zetaContinuationSocketToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      zetaContinuationSocketFromEventFlow (zetaContinuationSocketToEventFlow x) =
        zetaContinuationSocketFromEventFlow (zetaContinuationSocketToEventFlow y) :=
    congrArg zetaContinuationSocketFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (zetaContinuationSocket_round_trip x).symm
      (Eq.trans hread (zetaContinuationSocket_round_trip y)))

private theorem zetaContinuationSocket_field_faithful :
    forall x y : ZetaContinuationSocketUp,
      zetaContinuationSocketFields x = zetaContinuationSocketFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk B1 E1 A1 P1 F1 T1 G1 H1 C1 N1 =>
      cases y with
      | mk B2 E2 A2 P2 F2 T2 G2 H2 C2 N2 =>
          cases hfields
          rfl

instance zetaContinuationSocketBHistCarrier :
    BHistCarrier ZetaContinuationSocketUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := zetaContinuationSocketToEventFlow
  fromEventFlow := zetaContinuationSocketFromEventFlow

instance zetaContinuationSocketChapterTasteGate :
    ChapterTasteGate ZetaContinuationSocketUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change zetaContinuationSocketFromEventFlow (zetaContinuationSocketToEventFlow x) = some x
    exact zetaContinuationSocket_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (zetaContinuationSocketToEventFlow_injective heq)

instance zetaContinuationSocketFieldFaithful :
    FieldFaithful ZetaContinuationSocketUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := zetaContinuationSocketFields
  field_faithful := zetaContinuationSocket_field_faithful

instance zetaContinuationSocketNontrivial :
    BEDC.Meta.TasteGate.Nontrivial ZetaContinuationSocketUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ZetaContinuationSocketUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ZetaContinuationSocketUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem ZetaContinuationSocketTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate ZetaContinuationSocketUp) ∧
      Nonempty (FieldFaithful ZetaContinuationSocketUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial ZetaContinuationSocketUp) ∧
      (forall h : BHist,
        zetaContinuationSocketDecodeBHist (zetaContinuationSocketEncodeBHist h) = h) ∧
      (forall x : ZetaContinuationSocketUp,
        zetaContinuationSocketFromEventFlow (zetaContinuationSocketToEventFlow x) = some x) ∧
      (forall x y : ZetaContinuationSocketUp,
        zetaContinuationSocketToEventFlow x = zetaContinuationSocketToEventFlow y -> x = y) ∧
      zetaContinuationSocketEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨zetaContinuationSocketChapterTasteGate⟩
  constructor
  · exact ⟨zetaContinuationSocketFieldFaithful⟩
  constructor
  · exact ⟨zetaContinuationSocketNontrivial⟩
  constructor
  · exact zetaContinuationSocket_decode_encode
  constructor
  · exact zetaContinuationSocket_round_trip
  constructor
  · intro x y
    exact zetaContinuationSocketToEventFlow_injective
  · rfl

end BEDC.Derived.ZetaContinuationSocketUp
