import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DoubleCauchyDiagonalUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DoubleCauchyDiagonalUp : Type where
  | mk
      (doubleRegularCauchy rectangularWindow dyadicTolerance cofinalSchedule transport replay
        provenance localNameCert : BHist) :
      DoubleCauchyDiagonalUp
  deriving DecidableEq

def doubleCauchyDiagonalEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: doubleCauchyDiagonalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: doubleCauchyDiagonalEncodeBHist h

def doubleCauchyDiagonalDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (doubleCauchyDiagonalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (doubleCauchyDiagonalDecodeBHist tail)

private theorem doubleCauchyDiagonal_decode_encode_bhist :
    forall h : BHist, doubleCauchyDiagonalDecodeBHist (doubleCauchyDiagonalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def doubleCauchyDiagonalFields : DoubleCauchyDiagonalUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DoubleCauchyDiagonalUp.mk R W D K H C P N => [R, W, D, K, H, C, P, N]

def doubleCauchyDiagonalToEventFlow : DoubleCauchyDiagonalUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (doubleCauchyDiagonalFields x).map doubleCauchyDiagonalEncodeBHist

private def doubleCauchyDiagonalEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => doubleCauchyDiagonalEventAtDefault index rest

private def doubleCauchyDiagonalExactLength : Nat -> EventFlow -> Bool
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => true
  | Nat.zero, _event :: _rest => false
  | Nat.succ _index, [] => false
  | Nat.succ index, _event :: rest => doubleCauchyDiagonalExactLength index rest

def doubleCauchyDiagonalFromEventFlow (ef : EventFlow) : Option DoubleCauchyDiagonalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match doubleCauchyDiagonalExactLength 8 ef with
  | true =>
      some
        (DoubleCauchyDiagonalUp.mk
          (doubleCauchyDiagonalDecodeBHist (doubleCauchyDiagonalEventAtDefault 0 ef))
          (doubleCauchyDiagonalDecodeBHist (doubleCauchyDiagonalEventAtDefault 1 ef))
          (doubleCauchyDiagonalDecodeBHist (doubleCauchyDiagonalEventAtDefault 2 ef))
          (doubleCauchyDiagonalDecodeBHist (doubleCauchyDiagonalEventAtDefault 3 ef))
          (doubleCauchyDiagonalDecodeBHist (doubleCauchyDiagonalEventAtDefault 4 ef))
          (doubleCauchyDiagonalDecodeBHist (doubleCauchyDiagonalEventAtDefault 5 ef))
          (doubleCauchyDiagonalDecodeBHist (doubleCauchyDiagonalEventAtDefault 6 ef))
          (doubleCauchyDiagonalDecodeBHist (doubleCauchyDiagonalEventAtDefault 7 ef)))
  | false => none

private theorem doubleCauchyDiagonal_round_trip :
    forall x : DoubleCauchyDiagonalUp,
      doubleCauchyDiagonalFromEventFlow (doubleCauchyDiagonalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R W D K H C P N =>
      change
        some
          (DoubleCauchyDiagonalUp.mk
            (doubleCauchyDiagonalDecodeBHist (doubleCauchyDiagonalEncodeBHist R))
            (doubleCauchyDiagonalDecodeBHist (doubleCauchyDiagonalEncodeBHist W))
            (doubleCauchyDiagonalDecodeBHist (doubleCauchyDiagonalEncodeBHist D))
            (doubleCauchyDiagonalDecodeBHist (doubleCauchyDiagonalEncodeBHist K))
            (doubleCauchyDiagonalDecodeBHist (doubleCauchyDiagonalEncodeBHist H))
            (doubleCauchyDiagonalDecodeBHist (doubleCauchyDiagonalEncodeBHist C))
            (doubleCauchyDiagonalDecodeBHist (doubleCauchyDiagonalEncodeBHist P))
            (doubleCauchyDiagonalDecodeBHist (doubleCauchyDiagonalEncodeBHist N))) =
          some (DoubleCauchyDiagonalUp.mk R W D K H C P N)
      rw [doubleCauchyDiagonal_decode_encode_bhist R,
        doubleCauchyDiagonal_decode_encode_bhist W,
        doubleCauchyDiagonal_decode_encode_bhist D,
        doubleCauchyDiagonal_decode_encode_bhist K,
        doubleCauchyDiagonal_decode_encode_bhist H,
        doubleCauchyDiagonal_decode_encode_bhist C,
        doubleCauchyDiagonal_decode_encode_bhist P,
        doubleCauchyDiagonal_decode_encode_bhist N]

private theorem doubleCauchyDiagonalToEventFlow_injective {x y : DoubleCauchyDiagonalUp} :
    doubleCauchyDiagonalToEventFlow x = doubleCauchyDiagonalToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      doubleCauchyDiagonalFromEventFlow (doubleCauchyDiagonalToEventFlow x) =
        doubleCauchyDiagonalFromEventFlow (doubleCauchyDiagonalToEventFlow y) :=
    congrArg doubleCauchyDiagonalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (doubleCauchyDiagonal_round_trip x).symm
      (Eq.trans hread (doubleCauchyDiagonal_round_trip y)))

private theorem doubleCauchyDiagonal_field_faithful :
    forall x y : DoubleCauchyDiagonalUp,
      doubleCauchyDiagonalFields x = doubleCauchyDiagonalFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R1 W1 D1 K1 H1 C1 P1 N1 =>
      cases y with
      | mk R2 W2 D2 K2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance doubleCauchyDiagonalBHistCarrier : BHistCarrier DoubleCauchyDiagonalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := doubleCauchyDiagonalToEventFlow
  fromEventFlow := doubleCauchyDiagonalFromEventFlow

instance doubleCauchyDiagonalChapterTasteGate :
    ChapterTasteGate DoubleCauchyDiagonalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change doubleCauchyDiagonalFromEventFlow (doubleCauchyDiagonalToEventFlow x) = some x
    exact doubleCauchyDiagonal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (doubleCauchyDiagonalToEventFlow_injective heq)

instance doubleCauchyDiagonalFieldFaithful : FieldFaithful DoubleCauchyDiagonalUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := doubleCauchyDiagonalFields
  field_faithful := doubleCauchyDiagonal_field_faithful

instance doubleCauchyDiagonalNontrivial : Nontrivial DoubleCauchyDiagonalUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DoubleCauchyDiagonalUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      DoubleCauchyDiagonalUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DoubleCauchyDiagonalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  doubleCauchyDiagonalChapterTasteGate

theorem DoubleCauchyDiagonalTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate DoubleCauchyDiagonalUp) ∧
      Nonempty (FieldFaithful DoubleCauchyDiagonalUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial DoubleCauchyDiagonalUp) ∧
          (∀ h : BHist,
            doubleCauchyDiagonalDecodeBHist (doubleCauchyDiagonalEncodeBHist h) = h) ∧
            (∀ x : DoubleCauchyDiagonalUp,
              doubleCauchyDiagonalFromEventFlow (doubleCauchyDiagonalToEventFlow x) = some x) ∧
              (∀ x y : DoubleCauchyDiagonalUp,
                doubleCauchyDiagonalToEventFlow x = doubleCauchyDiagonalToEventFlow y → x = y) ∧
                doubleCauchyDiagonalEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨⟨doubleCauchyDiagonalChapterTasteGate⟩,
      ⟨doubleCauchyDiagonalFieldFaithful⟩,
      ⟨doubleCauchyDiagonalNontrivial⟩,
      doubleCauchyDiagonal_decode_encode_bhist,
      doubleCauchyDiagonal_round_trip,
      (fun _ _ heq => doubleCauchyDiagonalToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.DoubleCauchyDiagonalUp.TasteGate
