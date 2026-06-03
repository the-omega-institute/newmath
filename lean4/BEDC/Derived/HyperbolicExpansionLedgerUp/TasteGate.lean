import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HyperbolicExpansionLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HyperbolicExpansionLedgerUp : Type where
  | mk (F D G M B A H C P N : BHist) : HyperbolicExpansionLedgerUp
  deriving DecidableEq

def hyperbolicExpansionLedgerEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hyperbolicExpansionLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hyperbolicExpansionLedgerEncodeBHist h

def hyperbolicExpansionLedgerDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hyperbolicExpansionLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hyperbolicExpansionLedgerDecodeBHist tail)

private theorem HyperbolicExpansionLedgerTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      hyperbolicExpansionLedgerDecodeBHist
          (hyperbolicExpansionLedgerEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def hyperbolicExpansionLedgerFields :
    HyperbolicExpansionLedgerUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HyperbolicExpansionLedgerUp.mk F D G M B A H C P N =>
      [F, D, G, M, B, A, H, C, P, N]

def hyperbolicExpansionLedgerToEventFlow :
    HyperbolicExpansionLedgerUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (hyperbolicExpansionLedgerFields x).map hyperbolicExpansionLedgerEncodeBHist

private def hyperbolicExpansionLedgerEventAtDefault :
    Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      hyperbolicExpansionLedgerEventAtDefault index rest

def hyperbolicExpansionLedgerFromEventFlow
    (ef : EventFlow) : Option HyperbolicExpansionLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HyperbolicExpansionLedgerUp.mk
      (hyperbolicExpansionLedgerDecodeBHist
        (hyperbolicExpansionLedgerEventAtDefault 0 ef))
      (hyperbolicExpansionLedgerDecodeBHist
        (hyperbolicExpansionLedgerEventAtDefault 1 ef))
      (hyperbolicExpansionLedgerDecodeBHist
        (hyperbolicExpansionLedgerEventAtDefault 2 ef))
      (hyperbolicExpansionLedgerDecodeBHist
        (hyperbolicExpansionLedgerEventAtDefault 3 ef))
      (hyperbolicExpansionLedgerDecodeBHist
        (hyperbolicExpansionLedgerEventAtDefault 4 ef))
      (hyperbolicExpansionLedgerDecodeBHist
        (hyperbolicExpansionLedgerEventAtDefault 5 ef))
      (hyperbolicExpansionLedgerDecodeBHist
        (hyperbolicExpansionLedgerEventAtDefault 6 ef))
      (hyperbolicExpansionLedgerDecodeBHist
        (hyperbolicExpansionLedgerEventAtDefault 7 ef))
      (hyperbolicExpansionLedgerDecodeBHist
        (hyperbolicExpansionLedgerEventAtDefault 8 ef))
      (hyperbolicExpansionLedgerDecodeBHist
        (hyperbolicExpansionLedgerEventAtDefault 9 ef)))

private theorem HyperbolicExpansionLedgerTasteGate_single_carrier_alignment_round_trip
    (x : HyperbolicExpansionLedgerUp) :
    hyperbolicExpansionLedgerFromEventFlow
        (hyperbolicExpansionLedgerToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk F D G M B A H C P N =>
      change
        some
          (HyperbolicExpansionLedgerUp.mk
            (hyperbolicExpansionLedgerDecodeBHist
              (hyperbolicExpansionLedgerEncodeBHist F))
            (hyperbolicExpansionLedgerDecodeBHist
              (hyperbolicExpansionLedgerEncodeBHist D))
            (hyperbolicExpansionLedgerDecodeBHist
              (hyperbolicExpansionLedgerEncodeBHist G))
            (hyperbolicExpansionLedgerDecodeBHist
              (hyperbolicExpansionLedgerEncodeBHist M))
            (hyperbolicExpansionLedgerDecodeBHist
              (hyperbolicExpansionLedgerEncodeBHist B))
            (hyperbolicExpansionLedgerDecodeBHist
              (hyperbolicExpansionLedgerEncodeBHist A))
            (hyperbolicExpansionLedgerDecodeBHist
              (hyperbolicExpansionLedgerEncodeBHist H))
            (hyperbolicExpansionLedgerDecodeBHist
              (hyperbolicExpansionLedgerEncodeBHist C))
            (hyperbolicExpansionLedgerDecodeBHist
              (hyperbolicExpansionLedgerEncodeBHist P))
            (hyperbolicExpansionLedgerDecodeBHist
              (hyperbolicExpansionLedgerEncodeBHist N))) =
          some (HyperbolicExpansionLedgerUp.mk F D G M B A H C P N)
      rw [HyperbolicExpansionLedgerTasteGate_single_carrier_alignment_decode_encode F,
        HyperbolicExpansionLedgerTasteGate_single_carrier_alignment_decode_encode D,
        HyperbolicExpansionLedgerTasteGate_single_carrier_alignment_decode_encode G,
        HyperbolicExpansionLedgerTasteGate_single_carrier_alignment_decode_encode M,
        HyperbolicExpansionLedgerTasteGate_single_carrier_alignment_decode_encode B,
        HyperbolicExpansionLedgerTasteGate_single_carrier_alignment_decode_encode A,
        HyperbolicExpansionLedgerTasteGate_single_carrier_alignment_decode_encode H,
        HyperbolicExpansionLedgerTasteGate_single_carrier_alignment_decode_encode C,
        HyperbolicExpansionLedgerTasteGate_single_carrier_alignment_decode_encode P,
        HyperbolicExpansionLedgerTasteGate_single_carrier_alignment_decode_encode N]

private theorem HyperbolicExpansionLedgerTasteGate_single_carrier_alignment_injective
    {x y : HyperbolicExpansionLedgerUp} :
    hyperbolicExpansionLedgerToEventFlow x =
        hyperbolicExpansionLedgerToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hyperbolicExpansionLedgerFromEventFlow
          (hyperbolicExpansionLedgerToEventFlow x) =
        hyperbolicExpansionLedgerFromEventFlow
          (hyperbolicExpansionLedgerToEventFlow y) :=
    congrArg hyperbolicExpansionLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (HyperbolicExpansionLedgerTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (HyperbolicExpansionLedgerTasteGate_single_carrier_alignment_round_trip y)))

private theorem HyperbolicExpansionLedgerTasteGate_single_carrier_alignment_fields :
    forall x y : HyperbolicExpansionLedgerUp,
      hyperbolicExpansionLedgerFields x =
          hyperbolicExpansionLedgerFields y ->
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F1 D1 G1 M1 B1 A1 H1 C1 P1 N1 =>
      cases y with
      | mk F2 D2 G2 M2 B2 A2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance hyperbolicExpansionLedgerBHistCarrier :
    BHistCarrier HyperbolicExpansionLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hyperbolicExpansionLedgerToEventFlow
  fromEventFlow := hyperbolicExpansionLedgerFromEventFlow

instance hyperbolicExpansionLedgerChapterTasteGate :
    ChapterTasteGate HyperbolicExpansionLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      hyperbolicExpansionLedgerFromEventFlow
          (hyperbolicExpansionLedgerToEventFlow x) =
        some x
    exact HyperbolicExpansionLedgerTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (HyperbolicExpansionLedgerTasteGate_single_carrier_alignment_injective heq)

instance hyperbolicExpansionLedgerFieldFaithful :
    FieldFaithful HyperbolicExpansionLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := hyperbolicExpansionLedgerFields
  field_faithful :=
    HyperbolicExpansionLedgerTasteGate_single_carrier_alignment_fields

instance hyperbolicExpansionLedgerNontrivial :
    Nontrivial HyperbolicExpansionLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨HyperbolicExpansionLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      HyperbolicExpansionLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def HyperbolicExpansionLedgerTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate HyperbolicExpansionLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  hyperbolicExpansionLedgerChapterTasteGate

theorem HyperbolicExpansionLedgerTasteGate_single_carrier_alignment :
    (forall h : BHist,
      hyperbolicExpansionLedgerDecodeBHist
          (hyperbolicExpansionLedgerEncodeBHist h) = h) ∧
      (forall x : HyperbolicExpansionLedgerUp,
        hyperbolicExpansionLedgerFromEventFlow
            (hyperbolicExpansionLedgerToEventFlow x) =
          some x) ∧
        (forall x y : HyperbolicExpansionLedgerUp,
          hyperbolicExpansionLedgerToEventFlow x =
              hyperbolicExpansionLedgerToEventFlow y ->
            x = y) ∧
          hyperbolicExpansionLedgerEncodeBHist BHist.Empty =
            ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact HyperbolicExpansionLedgerTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact HyperbolicExpansionLedgerTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact HyperbolicExpansionLedgerTasteGate_single_carrier_alignment_injective heq
      · rfl

end BEDC.Derived.HyperbolicExpansionLedgerUp
