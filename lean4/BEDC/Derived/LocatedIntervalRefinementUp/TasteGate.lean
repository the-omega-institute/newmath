import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedIntervalRefinementUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedIntervalRefinementUp : Type where
  | mk (L U M F Q A H C P N : BHist) : LocatedIntervalRefinementUp
  deriving DecidableEq

def locatedIntervalRefinementEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedIntervalRefinementEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedIntervalRefinementEncodeBHist h

def locatedIntervalRefinementDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedIntervalRefinementDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedIntervalRefinementDecodeBHist tail)

private theorem LocatedIntervalRefinementTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      locatedIntervalRefinementDecodeBHist (locatedIntervalRefinementEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedIntervalRefinementFields : LocatedIntervalRefinementUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedIntervalRefinementUp.mk L U M F Q A H C P N => [L, U, M, F, Q, A, H, C, P, N]

def locatedIntervalRefinementToEventFlow : LocatedIntervalRefinementUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (locatedIntervalRefinementFields x).map locatedIntervalRefinementEncodeBHist

private def locatedIntervalRefinementEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatedIntervalRefinementEventAtDefault index rest

def locatedIntervalRefinementFromEventFlow
    (ef : EventFlow) : Option LocatedIntervalRefinementUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocatedIntervalRefinementUp.mk
      (locatedIntervalRefinementDecodeBHist (locatedIntervalRefinementEventAtDefault 0 ef))
      (locatedIntervalRefinementDecodeBHist (locatedIntervalRefinementEventAtDefault 1 ef))
      (locatedIntervalRefinementDecodeBHist (locatedIntervalRefinementEventAtDefault 2 ef))
      (locatedIntervalRefinementDecodeBHist (locatedIntervalRefinementEventAtDefault 3 ef))
      (locatedIntervalRefinementDecodeBHist (locatedIntervalRefinementEventAtDefault 4 ef))
      (locatedIntervalRefinementDecodeBHist (locatedIntervalRefinementEventAtDefault 5 ef))
      (locatedIntervalRefinementDecodeBHist (locatedIntervalRefinementEventAtDefault 6 ef))
      (locatedIntervalRefinementDecodeBHist (locatedIntervalRefinementEventAtDefault 7 ef))
      (locatedIntervalRefinementDecodeBHist (locatedIntervalRefinementEventAtDefault 8 ef))
      (locatedIntervalRefinementDecodeBHist (locatedIntervalRefinementEventAtDefault 9 ef)))

private theorem LocatedIntervalRefinementTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LocatedIntervalRefinementUp,
      locatedIntervalRefinementFromEventFlow (locatedIntervalRefinementToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L U M F Q A H C P N =>
      change
        some
          (LocatedIntervalRefinementUp.mk
            (locatedIntervalRefinementDecodeBHist (locatedIntervalRefinementEncodeBHist L))
            (locatedIntervalRefinementDecodeBHist (locatedIntervalRefinementEncodeBHist U))
            (locatedIntervalRefinementDecodeBHist (locatedIntervalRefinementEncodeBHist M))
            (locatedIntervalRefinementDecodeBHist (locatedIntervalRefinementEncodeBHist F))
            (locatedIntervalRefinementDecodeBHist (locatedIntervalRefinementEncodeBHist Q))
            (locatedIntervalRefinementDecodeBHist (locatedIntervalRefinementEncodeBHist A))
            (locatedIntervalRefinementDecodeBHist (locatedIntervalRefinementEncodeBHist H))
            (locatedIntervalRefinementDecodeBHist (locatedIntervalRefinementEncodeBHist C))
            (locatedIntervalRefinementDecodeBHist (locatedIntervalRefinementEncodeBHist P))
            (locatedIntervalRefinementDecodeBHist (locatedIntervalRefinementEncodeBHist N))) =
          some (LocatedIntervalRefinementUp.mk L U M F Q A H C P N)
      rw [LocatedIntervalRefinementTasteGate_single_carrier_alignment_decode_encode L,
        LocatedIntervalRefinementTasteGate_single_carrier_alignment_decode_encode U,
        LocatedIntervalRefinementTasteGate_single_carrier_alignment_decode_encode M,
        LocatedIntervalRefinementTasteGate_single_carrier_alignment_decode_encode F,
        LocatedIntervalRefinementTasteGate_single_carrier_alignment_decode_encode Q,
        LocatedIntervalRefinementTasteGate_single_carrier_alignment_decode_encode A,
        LocatedIntervalRefinementTasteGate_single_carrier_alignment_decode_encode H,
        LocatedIntervalRefinementTasteGate_single_carrier_alignment_decode_encode C,
        LocatedIntervalRefinementTasteGate_single_carrier_alignment_decode_encode P,
        LocatedIntervalRefinementTasteGate_single_carrier_alignment_decode_encode N]

private theorem LocatedIntervalRefinementTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LocatedIntervalRefinementUp} :
    locatedIntervalRefinementToEventFlow x = locatedIntervalRefinementToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedIntervalRefinementFromEventFlow (locatedIntervalRefinementToEventFlow x) =
        locatedIntervalRefinementFromEventFlow (locatedIntervalRefinementToEventFlow y) :=
    congrArg locatedIntervalRefinementFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (LocatedIntervalRefinementTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (LocatedIntervalRefinementTasteGate_single_carrier_alignment_round_trip y)))

instance locatedIntervalRefinementBHistCarrier :
    BHistCarrier LocatedIntervalRefinementUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedIntervalRefinementToEventFlow
  fromEventFlow := locatedIntervalRefinementFromEventFlow

instance locatedIntervalRefinementChapterTasteGate :
    ChapterTasteGate LocatedIntervalRefinementUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      locatedIntervalRefinementFromEventFlow (locatedIntervalRefinementToEventFlow x) =
        some x
    exact LocatedIntervalRefinementTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (LocatedIntervalRefinementTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate LocatedIntervalRefinementUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedIntervalRefinementChapterTasteGate

theorem LocatedIntervalRefinementTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      locatedIntervalRefinementDecodeBHist (locatedIntervalRefinementEncodeBHist h) = h) ∧
      (∀ x : LocatedIntervalRefinementUp,
        locatedIntervalRefinementFromEventFlow (locatedIntervalRefinementToEventFlow x) =
          some x) ∧
      (∀ x y : LocatedIntervalRefinementUp,
        locatedIntervalRefinementToEventFlow x = locatedIntervalRefinementToEventFlow y →
          x = y) ∧
      Nonempty (ChapterTasteGate LocatedIntervalRefinementUp) ∧
      Nonempty (BHistCarrier LocatedIntervalRefinementUp) ∧
      locatedIntervalRefinementEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨LocatedIntervalRefinementTasteGate_single_carrier_alignment_decode_encode,
      LocatedIntervalRefinementTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        LocatedIntervalRefinementTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      ⟨locatedIntervalRefinementChapterTasteGate⟩,
      ⟨locatedIntervalRefinementBHistCarrier⟩,
      rfl⟩

end BEDC.Derived.LocatedIntervalRefinementUp
