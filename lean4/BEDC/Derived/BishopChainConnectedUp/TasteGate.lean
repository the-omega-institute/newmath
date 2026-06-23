import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopChainConnectedUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopChainConnectedUp : Type where
  | mk (I A Z D J W R Q H C P N : BHist) : BishopChainConnectedUp

def bishopChainConnectedEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopChainConnectedEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopChainConnectedEncodeBHist h

def bishopChainConnectedDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopChainConnectedDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopChainConnectedDecodeBHist tail)

private theorem BishopChainConnectedTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      bishopChainConnectedDecodeBHist (bishopChainConnectedEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopChainConnectedFields : BishopChainConnectedUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopChainConnectedUp.mk I A Z D J W R Q H C P N => [I, A, Z, D, J, W, R, Q, H, C, P, N]

def bishopChainConnectedToEventFlow : BishopChainConnectedUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (bishopChainConnectedFields x).map bishopChainConnectedEncodeBHist

private def bishopChainConnectedEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopChainConnectedEventAtDefault index rest

def bishopChainConnectedFromEventFlow :
    EventFlow → Option BishopChainConnectedUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (BishopChainConnectedUp.mk
          (bishopChainConnectedDecodeBHist (bishopChainConnectedEventAtDefault 0 ef))
          (bishopChainConnectedDecodeBHist (bishopChainConnectedEventAtDefault 1 ef))
          (bishopChainConnectedDecodeBHist (bishopChainConnectedEventAtDefault 2 ef))
          (bishopChainConnectedDecodeBHist (bishopChainConnectedEventAtDefault 3 ef))
          (bishopChainConnectedDecodeBHist (bishopChainConnectedEventAtDefault 4 ef))
          (bishopChainConnectedDecodeBHist (bishopChainConnectedEventAtDefault 5 ef))
          (bishopChainConnectedDecodeBHist (bishopChainConnectedEventAtDefault 6 ef))
          (bishopChainConnectedDecodeBHist (bishopChainConnectedEventAtDefault 7 ef))
          (bishopChainConnectedDecodeBHist (bishopChainConnectedEventAtDefault 8 ef))
          (bishopChainConnectedDecodeBHist (bishopChainConnectedEventAtDefault 9 ef))
          (bishopChainConnectedDecodeBHist (bishopChainConnectedEventAtDefault 10 ef))
          (bishopChainConnectedDecodeBHist (bishopChainConnectedEventAtDefault 11 ef)))

private theorem BishopChainConnectedTasteGate_single_carrier_alignment_round_trip
    (x : BishopChainConnectedUp) :
    bishopChainConnectedFromEventFlow (bishopChainConnectedToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk I A Z D J W R Q H C P N =>
      change
        some
          (BishopChainConnectedUp.mk
            (bishopChainConnectedDecodeBHist (bishopChainConnectedEncodeBHist I))
            (bishopChainConnectedDecodeBHist (bishopChainConnectedEncodeBHist A))
            (bishopChainConnectedDecodeBHist (bishopChainConnectedEncodeBHist Z))
            (bishopChainConnectedDecodeBHist (bishopChainConnectedEncodeBHist D))
            (bishopChainConnectedDecodeBHist (bishopChainConnectedEncodeBHist J))
            (bishopChainConnectedDecodeBHist (bishopChainConnectedEncodeBHist W))
            (bishopChainConnectedDecodeBHist (bishopChainConnectedEncodeBHist R))
            (bishopChainConnectedDecodeBHist (bishopChainConnectedEncodeBHist Q))
            (bishopChainConnectedDecodeBHist (bishopChainConnectedEncodeBHist H))
            (bishopChainConnectedDecodeBHist (bishopChainConnectedEncodeBHist C))
            (bishopChainConnectedDecodeBHist (bishopChainConnectedEncodeBHist P))
            (bishopChainConnectedDecodeBHist (bishopChainConnectedEncodeBHist N))) =
          some (BishopChainConnectedUp.mk I A Z D J W R Q H C P N)
      rw [BishopChainConnectedTasteGate_single_carrier_alignment_decode I,
        BishopChainConnectedTasteGate_single_carrier_alignment_decode A,
        BishopChainConnectedTasteGate_single_carrier_alignment_decode Z,
        BishopChainConnectedTasteGate_single_carrier_alignment_decode D,
        BishopChainConnectedTasteGate_single_carrier_alignment_decode J,
        BishopChainConnectedTasteGate_single_carrier_alignment_decode W,
        BishopChainConnectedTasteGate_single_carrier_alignment_decode R,
        BishopChainConnectedTasteGate_single_carrier_alignment_decode Q,
        BishopChainConnectedTasteGate_single_carrier_alignment_decode H,
        BishopChainConnectedTasteGate_single_carrier_alignment_decode C,
        BishopChainConnectedTasteGate_single_carrier_alignment_decode P,
        BishopChainConnectedTasteGate_single_carrier_alignment_decode N]

private theorem BishopChainConnectedTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BishopChainConnectedUp} :
    bishopChainConnectedToEventFlow x = bishopChainConnectedToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopChainConnectedFromEventFlow (bishopChainConnectedToEventFlow x) =
        bishopChainConnectedFromEventFlow (bishopChainConnectedToEventFlow y) :=
    congrArg bishopChainConnectedFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BishopChainConnectedTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopChainConnectedTasteGate_single_carrier_alignment_round_trip y)))

instance bishopChainConnectedBHistCarrier :
    BHistCarrier BishopChainConnectedUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopChainConnectedToEventFlow
  fromEventFlow := bishopChainConnectedFromEventFlow

instance bishopChainConnectedChapterTasteGate :
    ChapterTasteGate BishopChainConnectedUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bishopChainConnectedFromEventFlow (bishopChainConnectedToEventFlow x) = some x
    exact BishopChainConnectedTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BishopChainConnectedTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate BishopChainConnectedUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopChainConnectedChapterTasteGate

theorem BishopChainConnectedTasteGate_single_carrier_alignment :
    (∀ h : BHist, bishopChainConnectedDecodeBHist (bishopChainConnectedEncodeBHist h) = h) ∧
      (∀ x : BishopChainConnectedUp,
        bishopChainConnectedFromEventFlow (bishopChainConnectedToEventFlow x) = some x) ∧
        (∀ x y : BishopChainConnectedUp,
          bishopChainConnectedToEventFlow x = bishopChainConnectedToEventFlow y → x = y) ∧
          bishopChainConnectedEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact BishopChainConnectedTasteGate_single_carrier_alignment_decode
  · constructor
    · exact BishopChainConnectedTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact BishopChainConnectedTasteGate_single_carrier_alignment_toEventFlow_injective heq
      · rfl

end BEDC.Derived.BishopChainConnectedUp.TasteGate
