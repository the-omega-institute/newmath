import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopLocatedIntervalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopLocatedIntervalUp : Type where
  | mk (L U D Q S R E H C P N : BHist) : BishopLocatedIntervalUp
  deriving DecidableEq

def bishopLocatedIntervalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopLocatedIntervalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopLocatedIntervalEncodeBHist h

def bishopLocatedIntervalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopLocatedIntervalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopLocatedIntervalDecodeBHist tail)

private theorem BishopLocatedIntervalTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      bishopLocatedIntervalDecodeBHist (bishopLocatedIntervalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopLocatedIntervalFields : BishopLocatedIntervalUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopLocatedIntervalUp.mk L U D Q S R E H C P N => [L, U, D, Q, S, R, E, H, C, P, N]

def bishopLocatedIntervalToEventFlow : BishopLocatedIntervalUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (bishopLocatedIntervalFields x).map bishopLocatedIntervalEncodeBHist

private def bishopLocatedIntervalEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopLocatedIntervalEventAtDefault index rest

def bishopLocatedIntervalFromEventFlow (ef : EventFlow) : Option BishopLocatedIntervalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopLocatedIntervalUp.mk
      (bishopLocatedIntervalDecodeBHist (bishopLocatedIntervalEventAtDefault 0 ef))
      (bishopLocatedIntervalDecodeBHist (bishopLocatedIntervalEventAtDefault 1 ef))
      (bishopLocatedIntervalDecodeBHist (bishopLocatedIntervalEventAtDefault 2 ef))
      (bishopLocatedIntervalDecodeBHist (bishopLocatedIntervalEventAtDefault 3 ef))
      (bishopLocatedIntervalDecodeBHist (bishopLocatedIntervalEventAtDefault 4 ef))
      (bishopLocatedIntervalDecodeBHist (bishopLocatedIntervalEventAtDefault 5 ef))
      (bishopLocatedIntervalDecodeBHist (bishopLocatedIntervalEventAtDefault 6 ef))
      (bishopLocatedIntervalDecodeBHist (bishopLocatedIntervalEventAtDefault 7 ef))
      (bishopLocatedIntervalDecodeBHist (bishopLocatedIntervalEventAtDefault 8 ef))
      (bishopLocatedIntervalDecodeBHist (bishopLocatedIntervalEventAtDefault 9 ef))
      (bishopLocatedIntervalDecodeBHist (bishopLocatedIntervalEventAtDefault 10 ef)))

private theorem BishopLocatedIntervalTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BishopLocatedIntervalUp,
      bishopLocatedIntervalFromEventFlow (bishopLocatedIntervalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L U D Q S R E H C P N =>
      change
        some
            (BishopLocatedIntervalUp.mk
              (bishopLocatedIntervalDecodeBHist (bishopLocatedIntervalEncodeBHist L))
              (bishopLocatedIntervalDecodeBHist (bishopLocatedIntervalEncodeBHist U))
              (bishopLocatedIntervalDecodeBHist (bishopLocatedIntervalEncodeBHist D))
              (bishopLocatedIntervalDecodeBHist (bishopLocatedIntervalEncodeBHist Q))
              (bishopLocatedIntervalDecodeBHist (bishopLocatedIntervalEncodeBHist S))
              (bishopLocatedIntervalDecodeBHist (bishopLocatedIntervalEncodeBHist R))
              (bishopLocatedIntervalDecodeBHist (bishopLocatedIntervalEncodeBHist E))
              (bishopLocatedIntervalDecodeBHist (bishopLocatedIntervalEncodeBHist H))
              (bishopLocatedIntervalDecodeBHist (bishopLocatedIntervalEncodeBHist C))
              (bishopLocatedIntervalDecodeBHist (bishopLocatedIntervalEncodeBHist P))
              (bishopLocatedIntervalDecodeBHist (bishopLocatedIntervalEncodeBHist N))) =
          some (BishopLocatedIntervalUp.mk L U D Q S R E H C P N)
      rw [BishopLocatedIntervalTasteGate_single_carrier_alignment_decode L,
        BishopLocatedIntervalTasteGate_single_carrier_alignment_decode U,
        BishopLocatedIntervalTasteGate_single_carrier_alignment_decode D,
        BishopLocatedIntervalTasteGate_single_carrier_alignment_decode Q,
        BishopLocatedIntervalTasteGate_single_carrier_alignment_decode S,
        BishopLocatedIntervalTasteGate_single_carrier_alignment_decode R,
        BishopLocatedIntervalTasteGate_single_carrier_alignment_decode E,
        BishopLocatedIntervalTasteGate_single_carrier_alignment_decode H,
        BishopLocatedIntervalTasteGate_single_carrier_alignment_decode C,
        BishopLocatedIntervalTasteGate_single_carrier_alignment_decode P,
        BishopLocatedIntervalTasteGate_single_carrier_alignment_decode N]

private theorem BishopLocatedIntervalTasteGate_single_carrier_alignment_injective
    {x y : BishopLocatedIntervalUp} :
    bishopLocatedIntervalToEventFlow x = bishopLocatedIntervalToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopLocatedIntervalFromEventFlow (bishopLocatedIntervalToEventFlow x) =
        bishopLocatedIntervalFromEventFlow (bishopLocatedIntervalToEventFlow y) :=
    congrArg bishopLocatedIntervalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BishopLocatedIntervalTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopLocatedIntervalTasteGate_single_carrier_alignment_round_trip y)))

instance bishopLocatedIntervalBHistCarrier : BHistCarrier BishopLocatedIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopLocatedIntervalToEventFlow
  fromEventFlow := bishopLocatedIntervalFromEventFlow

instance bishopLocatedIntervalChapterTasteGate : ChapterTasteGate BishopLocatedIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bishopLocatedIntervalFromEventFlow (bishopLocatedIntervalToEventFlow x) = some x
    exact BishopLocatedIntervalTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BishopLocatedIntervalTasteGate_single_carrier_alignment_injective heq)

theorem BishopLocatedIntervalTasteGate_single_carrier_alignment :
    (∀ h : BHist, bishopLocatedIntervalDecodeBHist (bishopLocatedIntervalEncodeBHist h) = h) ∧
      (∀ x : BishopLocatedIntervalUp,
        bishopLocatedIntervalFromEventFlow (bishopLocatedIntervalToEventFlow x) = some x) ∧
        (∀ x y : BishopLocatedIntervalUp,
          bishopLocatedIntervalToEventFlow x = bishopLocatedIntervalToEventFlow y → x = y) ∧
          bishopLocatedIntervalEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨BishopLocatedIntervalTasteGate_single_carrier_alignment_decode,
      ⟨BishopLocatedIntervalTasteGate_single_carrier_alignment_round_trip,
        ⟨fun _ _ heq =>
          BishopLocatedIntervalTasteGate_single_carrier_alignment_injective heq,
          rfl⟩⟩⟩

end BEDC.Derived.BishopLocatedIntervalUp
