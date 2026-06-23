import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedCauchyIntervalRefinementUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedCauchyIntervalRefinementUp : Type where
  | mk (I B D S R A W H C P N : BHist) : LocatedCauchyIntervalRefinementUp
  deriving DecidableEq

def locatedCauchyIntervalRefinementEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedCauchyIntervalRefinementEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedCauchyIntervalRefinementEncodeBHist h

def locatedCauchyIntervalRefinementDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedCauchyIntervalRefinementDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedCauchyIntervalRefinementDecodeBHist tail)

private theorem locatedCauchyIntervalRefinementDecode_encode_bhist :
    ∀ h : BHist,
      locatedCauchyIntervalRefinementDecodeBHist
          (locatedCauchyIntervalRefinementEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedCauchyIntervalRefinementFields :
    LocatedCauchyIntervalRefinementUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedCauchyIntervalRefinementUp.mk I B D S R A W H C P N =>
      [I, B, D, S, R, A, W, H, C, P, N]

def locatedCauchyIntervalRefinementToEventFlow :
    LocatedCauchyIntervalRefinementUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (locatedCauchyIntervalRefinementFields x).map
        locatedCauchyIntervalRefinementEncodeBHist

private def locatedCauchyIntervalRefinementEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      locatedCauchyIntervalRefinementEventAtDefault index rest

def locatedCauchyIntervalRefinementFromEventFlow
    (ef : EventFlow) : Option LocatedCauchyIntervalRefinementUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocatedCauchyIntervalRefinementUp.mk
      (locatedCauchyIntervalRefinementDecodeBHist
        (locatedCauchyIntervalRefinementEventAtDefault 0 ef))
      (locatedCauchyIntervalRefinementDecodeBHist
        (locatedCauchyIntervalRefinementEventAtDefault 1 ef))
      (locatedCauchyIntervalRefinementDecodeBHist
        (locatedCauchyIntervalRefinementEventAtDefault 2 ef))
      (locatedCauchyIntervalRefinementDecodeBHist
        (locatedCauchyIntervalRefinementEventAtDefault 3 ef))
      (locatedCauchyIntervalRefinementDecodeBHist
        (locatedCauchyIntervalRefinementEventAtDefault 4 ef))
      (locatedCauchyIntervalRefinementDecodeBHist
        (locatedCauchyIntervalRefinementEventAtDefault 5 ef))
      (locatedCauchyIntervalRefinementDecodeBHist
        (locatedCauchyIntervalRefinementEventAtDefault 6 ef))
      (locatedCauchyIntervalRefinementDecodeBHist
        (locatedCauchyIntervalRefinementEventAtDefault 7 ef))
      (locatedCauchyIntervalRefinementDecodeBHist
        (locatedCauchyIntervalRefinementEventAtDefault 8 ef))
      (locatedCauchyIntervalRefinementDecodeBHist
        (locatedCauchyIntervalRefinementEventAtDefault 9 ef))
      (locatedCauchyIntervalRefinementDecodeBHist
        (locatedCauchyIntervalRefinementEventAtDefault 10 ef)))

private theorem locatedCauchyIntervalRefinement_round_trip :
    ∀ x : LocatedCauchyIntervalRefinementUp,
      locatedCauchyIntervalRefinementFromEventFlow
          (locatedCauchyIntervalRefinementToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I B D S R A W H C P N =>
      change
        some
          (LocatedCauchyIntervalRefinementUp.mk
            (locatedCauchyIntervalRefinementDecodeBHist
              (locatedCauchyIntervalRefinementEncodeBHist I))
            (locatedCauchyIntervalRefinementDecodeBHist
              (locatedCauchyIntervalRefinementEncodeBHist B))
            (locatedCauchyIntervalRefinementDecodeBHist
              (locatedCauchyIntervalRefinementEncodeBHist D))
            (locatedCauchyIntervalRefinementDecodeBHist
              (locatedCauchyIntervalRefinementEncodeBHist S))
            (locatedCauchyIntervalRefinementDecodeBHist
              (locatedCauchyIntervalRefinementEncodeBHist R))
            (locatedCauchyIntervalRefinementDecodeBHist
              (locatedCauchyIntervalRefinementEncodeBHist A))
            (locatedCauchyIntervalRefinementDecodeBHist
              (locatedCauchyIntervalRefinementEncodeBHist W))
            (locatedCauchyIntervalRefinementDecodeBHist
              (locatedCauchyIntervalRefinementEncodeBHist H))
            (locatedCauchyIntervalRefinementDecodeBHist
              (locatedCauchyIntervalRefinementEncodeBHist C))
            (locatedCauchyIntervalRefinementDecodeBHist
              (locatedCauchyIntervalRefinementEncodeBHist P))
            (locatedCauchyIntervalRefinementDecodeBHist
              (locatedCauchyIntervalRefinementEncodeBHist N))) =
          some (LocatedCauchyIntervalRefinementUp.mk I B D S R A W H C P N)
      rw [locatedCauchyIntervalRefinementDecode_encode_bhist I,
        locatedCauchyIntervalRefinementDecode_encode_bhist B,
        locatedCauchyIntervalRefinementDecode_encode_bhist D,
        locatedCauchyIntervalRefinementDecode_encode_bhist S,
        locatedCauchyIntervalRefinementDecode_encode_bhist R,
        locatedCauchyIntervalRefinementDecode_encode_bhist A,
        locatedCauchyIntervalRefinementDecode_encode_bhist W,
        locatedCauchyIntervalRefinementDecode_encode_bhist H,
        locatedCauchyIntervalRefinementDecode_encode_bhist C,
        locatedCauchyIntervalRefinementDecode_encode_bhist P,
        locatedCauchyIntervalRefinementDecode_encode_bhist N]

private theorem locatedCauchyIntervalRefinementToEventFlow_injective
    {x y : LocatedCauchyIntervalRefinementUp} :
    locatedCauchyIntervalRefinementToEventFlow x =
      locatedCauchyIntervalRefinementToEventFlow y →
    x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedCauchyIntervalRefinementFromEventFlow
          (locatedCauchyIntervalRefinementToEventFlow x) =
        locatedCauchyIntervalRefinementFromEventFlow
          (locatedCauchyIntervalRefinementToEventFlow y) :=
    congrArg locatedCauchyIntervalRefinementFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (locatedCauchyIntervalRefinement_round_trip x).symm
      (Eq.trans hread (locatedCauchyIntervalRefinement_round_trip y)))

instance locatedCauchyIntervalRefinementBHistCarrier :
    BHistCarrier LocatedCauchyIntervalRefinementUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedCauchyIntervalRefinementToEventFlow
  fromEventFlow := locatedCauchyIntervalRefinementFromEventFlow

instance locatedCauchyIntervalRefinementChapterTasteGate :
    ChapterTasteGate LocatedCauchyIntervalRefinementUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      locatedCauchyIntervalRefinementFromEventFlow
          (locatedCauchyIntervalRefinementToEventFlow x) =
        some x
    exact locatedCauchyIntervalRefinement_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locatedCauchyIntervalRefinementToEventFlow_injective heq)

def taste_gate : ChapterTasteGate LocatedCauchyIntervalRefinementUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedCauchyIntervalRefinementChapterTasteGate

theorem LocatedCauchyIntervalRefinementTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      locatedCauchyIntervalRefinementDecodeBHist
        (locatedCauchyIntervalRefinementEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier LocatedCauchyIntervalRefinementUp) ∧
        Nonempty (ChapterTasteGate LocatedCauchyIntervalRefinementUp) ∧
          locatedCauchyIntervalRefinementEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨locatedCauchyIntervalRefinementDecode_encode_bhist,
      ⟨locatedCauchyIntervalRefinementBHistCarrier⟩,
      ⟨locatedCauchyIntervalRefinementChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.LocatedCauchyIntervalRefinementUp
