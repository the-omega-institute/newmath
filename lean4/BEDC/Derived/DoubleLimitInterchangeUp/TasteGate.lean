import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DoubleLimitInterchangeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DoubleLimitInterchangeUp : Type where
  | mk (O J D Delta R0 R1 E H C P N : BHist) : DoubleLimitInterchangeUp
  deriving DecidableEq

def doubleLimitInterchangeEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: doubleLimitInterchangeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: doubleLimitInterchangeEncodeBHist h

def doubleLimitInterchangeDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (doubleLimitInterchangeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (doubleLimitInterchangeDecodeBHist tail)

private theorem DoubleLimitInterchangeTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      doubleLimitInterchangeDecodeBHist (doubleLimitInterchangeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def doubleLimitInterchangeFields : DoubleLimitInterchangeUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DoubleLimitInterchangeUp.mk O J D Delta R0 R1 E H C P N =>
      [O, J, D, Delta, R0, R1, E, H, C, P, N]

def doubleLimitInterchangeToEventFlow : DoubleLimitInterchangeUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (doubleLimitInterchangeFields x).map doubleLimitInterchangeEncodeBHist

private def doubleLimitInterchangeEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => doubleLimitInterchangeEventAtDefault index rest

def doubleLimitInterchangeFromEventFlow
    (ef : EventFlow) : Option DoubleLimitInterchangeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DoubleLimitInterchangeUp.mk
      (doubleLimitInterchangeDecodeBHist (doubleLimitInterchangeEventAtDefault 0 ef))
      (doubleLimitInterchangeDecodeBHist (doubleLimitInterchangeEventAtDefault 1 ef))
      (doubleLimitInterchangeDecodeBHist (doubleLimitInterchangeEventAtDefault 2 ef))
      (doubleLimitInterchangeDecodeBHist (doubleLimitInterchangeEventAtDefault 3 ef))
      (doubleLimitInterchangeDecodeBHist (doubleLimitInterchangeEventAtDefault 4 ef))
      (doubleLimitInterchangeDecodeBHist (doubleLimitInterchangeEventAtDefault 5 ef))
      (doubleLimitInterchangeDecodeBHist (doubleLimitInterchangeEventAtDefault 6 ef))
      (doubleLimitInterchangeDecodeBHist (doubleLimitInterchangeEventAtDefault 7 ef))
      (doubleLimitInterchangeDecodeBHist (doubleLimitInterchangeEventAtDefault 8 ef))
      (doubleLimitInterchangeDecodeBHist (doubleLimitInterchangeEventAtDefault 9 ef))
      (doubleLimitInterchangeDecodeBHist (doubleLimitInterchangeEventAtDefault 10 ef)))

private theorem DoubleLimitInterchangeTasteGate_single_carrier_alignment_round_trip :
    forall x : DoubleLimitInterchangeUp,
      doubleLimitInterchangeFromEventFlow (doubleLimitInterchangeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk O J D Delta R0 R1 E H C P N =>
      change
        some
          (DoubleLimitInterchangeUp.mk
            (doubleLimitInterchangeDecodeBHist (doubleLimitInterchangeEncodeBHist O))
            (doubleLimitInterchangeDecodeBHist (doubleLimitInterchangeEncodeBHist J))
            (doubleLimitInterchangeDecodeBHist (doubleLimitInterchangeEncodeBHist D))
            (doubleLimitInterchangeDecodeBHist (doubleLimitInterchangeEncodeBHist Delta))
            (doubleLimitInterchangeDecodeBHist (doubleLimitInterchangeEncodeBHist R0))
            (doubleLimitInterchangeDecodeBHist (doubleLimitInterchangeEncodeBHist R1))
            (doubleLimitInterchangeDecodeBHist (doubleLimitInterchangeEncodeBHist E))
            (doubleLimitInterchangeDecodeBHist (doubleLimitInterchangeEncodeBHist H))
            (doubleLimitInterchangeDecodeBHist (doubleLimitInterchangeEncodeBHist C))
            (doubleLimitInterchangeDecodeBHist (doubleLimitInterchangeEncodeBHist P))
            (doubleLimitInterchangeDecodeBHist (doubleLimitInterchangeEncodeBHist N))) =
          some (DoubleLimitInterchangeUp.mk O J D Delta R0 R1 E H C P N)
      rw [DoubleLimitInterchangeTasteGate_single_carrier_alignment_decode O,
        DoubleLimitInterchangeTasteGate_single_carrier_alignment_decode J,
        DoubleLimitInterchangeTasteGate_single_carrier_alignment_decode D,
        DoubleLimitInterchangeTasteGate_single_carrier_alignment_decode Delta,
        DoubleLimitInterchangeTasteGate_single_carrier_alignment_decode R0,
        DoubleLimitInterchangeTasteGate_single_carrier_alignment_decode R1,
        DoubleLimitInterchangeTasteGate_single_carrier_alignment_decode E,
        DoubleLimitInterchangeTasteGate_single_carrier_alignment_decode H,
        DoubleLimitInterchangeTasteGate_single_carrier_alignment_decode C,
        DoubleLimitInterchangeTasteGate_single_carrier_alignment_decode P,
        DoubleLimitInterchangeTasteGate_single_carrier_alignment_decode N]

private theorem DoubleLimitInterchangeTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DoubleLimitInterchangeUp} :
    doubleLimitInterchangeToEventFlow x = doubleLimitInterchangeToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      doubleLimitInterchangeFromEventFlow (doubleLimitInterchangeToEventFlow x) =
        doubleLimitInterchangeFromEventFlow (doubleLimitInterchangeToEventFlow y) :=
    congrArg doubleLimitInterchangeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (DoubleLimitInterchangeTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (DoubleLimitInterchangeTasteGate_single_carrier_alignment_round_trip y)))

private theorem DoubleLimitInterchangeTasteGate_single_carrier_alignment_fields :
    forall x y : DoubleLimitInterchangeUp,
      doubleLimitInterchangeFields x = doubleLimitInterchangeFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk O1 J1 D1 Delta1 R01 R11 E1 H1 C1 P1 N1 =>
      cases y with
      | mk O2 J2 D2 Delta2 R02 R12 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance doubleLimitInterchangeBHistCarrier :
    BHistCarrier DoubleLimitInterchangeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := doubleLimitInterchangeToEventFlow
  fromEventFlow := doubleLimitInterchangeFromEventFlow

instance doubleLimitInterchangeChapterTasteGate :
    ChapterTasteGate DoubleLimitInterchangeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change doubleLimitInterchangeFromEventFlow (doubleLimitInterchangeToEventFlow x) =
      some x
    exact DoubleLimitInterchangeTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (DoubleLimitInterchangeTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate DoubleLimitInterchangeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  doubleLimitInterchangeChapterTasteGate

theorem DoubleLimitInterchangeTasteGate_single_carrier_alignment :
    (forall h : BHist, doubleLimitInterchangeDecodeBHist
      (doubleLimitInterchangeEncodeBHist h) = h) ∧
      (forall x : DoubleLimitInterchangeUp,
        doubleLimitInterchangeFromEventFlow (doubleLimitInterchangeToEventFlow x) = some x) ∧
        (forall x y : DoubleLimitInterchangeUp,
          doubleLimitInterchangeToEventFlow x = doubleLimitInterchangeToEventFlow y -> x = y) ∧
          doubleLimitInterchangeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨DoubleLimitInterchangeTasteGate_single_carrier_alignment_decode,
      DoubleLimitInterchangeTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        DoubleLimitInterchangeTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.DoubleLimitInterchangeUp
