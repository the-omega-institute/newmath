import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HorosphereFlowLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HorosphereFlowLedgerUp : Type where
  | mk (O S B T L H C P N : BHist) : HorosphereFlowLedgerUp
  deriving DecidableEq

def horosphereFlowLedgerEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: horosphereFlowLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: horosphereFlowLedgerEncodeBHist h

def horosphereFlowLedgerDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (horosphereFlowLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (horosphereFlowLedgerDecodeBHist tail)

private theorem horosphereFlowLedger_decode_encode_bhist :
    forall h : BHist,
      horosphereFlowLedgerDecodeBHist (horosphereFlowLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def horosphereFlowLedgerFields : HorosphereFlowLedgerUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HorosphereFlowLedgerUp.mk O S B T L H C P N => [O, S, B, T, L, H, C, P, N]

def horosphereFlowLedgerToEventFlow : HorosphereFlowLedgerUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (horosphereFlowLedgerFields x).map horosphereFlowLedgerEncodeBHist

private def horosphereFlowLedgerEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => horosphereFlowLedgerEventAtDefault index rest

def horosphereFlowLedgerFromEventFlow
    (ef : EventFlow) : Option HorosphereFlowLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HorosphereFlowLedgerUp.mk
      (horosphereFlowLedgerDecodeBHist (horosphereFlowLedgerEventAtDefault 0 ef))
      (horosphereFlowLedgerDecodeBHist (horosphereFlowLedgerEventAtDefault 1 ef))
      (horosphereFlowLedgerDecodeBHist (horosphereFlowLedgerEventAtDefault 2 ef))
      (horosphereFlowLedgerDecodeBHist (horosphereFlowLedgerEventAtDefault 3 ef))
      (horosphereFlowLedgerDecodeBHist (horosphereFlowLedgerEventAtDefault 4 ef))
      (horosphereFlowLedgerDecodeBHist (horosphereFlowLedgerEventAtDefault 5 ef))
      (horosphereFlowLedgerDecodeBHist (horosphereFlowLedgerEventAtDefault 6 ef))
      (horosphereFlowLedgerDecodeBHist (horosphereFlowLedgerEventAtDefault 7 ef))
      (horosphereFlowLedgerDecodeBHist (horosphereFlowLedgerEventAtDefault 8 ef)))

private theorem horosphereFlowLedger_round_trip :
    forall x : HorosphereFlowLedgerUp,
      horosphereFlowLedgerFromEventFlow (horosphereFlowLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk O S B T L H C P N =>
      change
        some
            (HorosphereFlowLedgerUp.mk
              (horosphereFlowLedgerDecodeBHist (horosphereFlowLedgerEncodeBHist O))
              (horosphereFlowLedgerDecodeBHist (horosphereFlowLedgerEncodeBHist S))
              (horosphereFlowLedgerDecodeBHist (horosphereFlowLedgerEncodeBHist B))
              (horosphereFlowLedgerDecodeBHist (horosphereFlowLedgerEncodeBHist T))
              (horosphereFlowLedgerDecodeBHist (horosphereFlowLedgerEncodeBHist L))
              (horosphereFlowLedgerDecodeBHist (horosphereFlowLedgerEncodeBHist H))
              (horosphereFlowLedgerDecodeBHist (horosphereFlowLedgerEncodeBHist C))
              (horosphereFlowLedgerDecodeBHist (horosphereFlowLedgerEncodeBHist P))
              (horosphereFlowLedgerDecodeBHist (horosphereFlowLedgerEncodeBHist N))) =
          some (HorosphereFlowLedgerUp.mk O S B T L H C P N)
      rw [horosphereFlowLedger_decode_encode_bhist O,
        horosphereFlowLedger_decode_encode_bhist S,
        horosphereFlowLedger_decode_encode_bhist B,
        horosphereFlowLedger_decode_encode_bhist T,
        horosphereFlowLedger_decode_encode_bhist L,
        horosphereFlowLedger_decode_encode_bhist H,
        horosphereFlowLedger_decode_encode_bhist C,
        horosphereFlowLedger_decode_encode_bhist P,
        horosphereFlowLedger_decode_encode_bhist N]

private theorem horosphereFlowLedgerToEventFlow_injective {x y : HorosphereFlowLedgerUp} :
    horosphereFlowLedgerToEventFlow x = horosphereFlowLedgerToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      horosphereFlowLedgerFromEventFlow (horosphereFlowLedgerToEventFlow x) =
        horosphereFlowLedgerFromEventFlow (horosphereFlowLedgerToEventFlow y) :=
    congrArg horosphereFlowLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (horosphereFlowLedger_round_trip x).symm
      (Eq.trans hread (horosphereFlowLedger_round_trip y)))

private theorem horosphereFlowLedger_fields_faithful :
    forall x y : HorosphereFlowLedgerUp,
      horosphereFlowLedgerFields x = horosphereFlowLedgerFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk O1 S1 B1 T1 L1 H1 C1 P1 N1 =>
      cases y with
      | mk O2 S2 B2 T2 L2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance horosphereFlowLedgerBHistCarrier : BHistCarrier HorosphereFlowLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := horosphereFlowLedgerToEventFlow
  fromEventFlow := horosphereFlowLedgerFromEventFlow

instance horosphereFlowLedgerChapterTasteGate :
    ChapterTasteGate HorosphereFlowLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change horosphereFlowLedgerFromEventFlow (horosphereFlowLedgerToEventFlow x) = some x
    exact horosphereFlowLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (horosphereFlowLedgerToEventFlow_injective heq)

instance horosphereFlowLedgerFieldFaithful : FieldFaithful HorosphereFlowLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := horosphereFlowLedgerFields
  field_faithful := horosphereFlowLedger_fields_faithful

instance horosphereFlowLedgerNontrivial : Nontrivial HorosphereFlowLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨HorosphereFlowLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      HorosphereFlowLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate HorosphereFlowLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  horosphereFlowLedgerChapterTasteGate

theorem HorosphereFlowLedgerTasteGate_single_carrier_alignment :
    (forall h : BHist,
      horosphereFlowLedgerDecodeBHist (horosphereFlowLedgerEncodeBHist h) = h) ∧
      (forall x : HorosphereFlowLedgerUp,
        horosphereFlowLedgerFromEventFlow (horosphereFlowLedgerToEventFlow x) = some x) ∧
        (forall x y : HorosphereFlowLedgerUp,
          horosphereFlowLedgerToEventFlow x = horosphereFlowLedgerToEventFlow y -> x = y) ∧
          horosphereFlowLedgerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨horosphereFlowLedger_decode_encode_bhist,
      horosphereFlowLedger_round_trip,
      (fun _ _ heq => horosphereFlowLedgerToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.HorosphereFlowLedgerUp
