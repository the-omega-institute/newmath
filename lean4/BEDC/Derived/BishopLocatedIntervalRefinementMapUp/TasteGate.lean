import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopLocatedIntervalRefinementMapUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopLocatedIntervalRefinementMapUp : Type where
  | mk (I J R D W S E H C P N : BHist) : BishopLocatedIntervalRefinementMapUp
  deriving DecidableEq

def bishopLocatedIntervalRefinementMapEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopLocatedIntervalRefinementMapEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopLocatedIntervalRefinementMapEncodeBHist h

def bishopLocatedIntervalRefinementMapDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopLocatedIntervalRefinementMapDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopLocatedIntervalRefinementMapDecodeBHist tail)

private theorem BishopLocatedIntervalRefinementMapTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      bishopLocatedIntervalRefinementMapDecodeBHist
        (bishopLocatedIntervalRefinementMapEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopLocatedIntervalRefinementMapFields :
    BishopLocatedIntervalRefinementMapUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopLocatedIntervalRefinementMapUp.mk I J R D W S E H C P N =>
      [I, J, R, D, W, S, E, H, C, P, N]

def bishopLocatedIntervalRefinementMapToEventFlow :
    BishopLocatedIntervalRefinementMapUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (bishopLocatedIntervalRefinementMapFields x).map
        bishopLocatedIntervalRefinementMapEncodeBHist

private def bishopLocatedIntervalRefinementMapEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      bishopLocatedIntervalRefinementMapEventAtDefault index rest

def bishopLocatedIntervalRefinementMapFromEventFlow
    (ef : EventFlow) : Option BishopLocatedIntervalRefinementMapUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopLocatedIntervalRefinementMapUp.mk
      (bishopLocatedIntervalRefinementMapDecodeBHist
        (bishopLocatedIntervalRefinementMapEventAtDefault 0 ef))
      (bishopLocatedIntervalRefinementMapDecodeBHist
        (bishopLocatedIntervalRefinementMapEventAtDefault 1 ef))
      (bishopLocatedIntervalRefinementMapDecodeBHist
        (bishopLocatedIntervalRefinementMapEventAtDefault 2 ef))
      (bishopLocatedIntervalRefinementMapDecodeBHist
        (bishopLocatedIntervalRefinementMapEventAtDefault 3 ef))
      (bishopLocatedIntervalRefinementMapDecodeBHist
        (bishopLocatedIntervalRefinementMapEventAtDefault 4 ef))
      (bishopLocatedIntervalRefinementMapDecodeBHist
        (bishopLocatedIntervalRefinementMapEventAtDefault 5 ef))
      (bishopLocatedIntervalRefinementMapDecodeBHist
        (bishopLocatedIntervalRefinementMapEventAtDefault 6 ef))
      (bishopLocatedIntervalRefinementMapDecodeBHist
        (bishopLocatedIntervalRefinementMapEventAtDefault 7 ef))
      (bishopLocatedIntervalRefinementMapDecodeBHist
        (bishopLocatedIntervalRefinementMapEventAtDefault 8 ef))
      (bishopLocatedIntervalRefinementMapDecodeBHist
        (bishopLocatedIntervalRefinementMapEventAtDefault 9 ef))
      (bishopLocatedIntervalRefinementMapDecodeBHist
        (bishopLocatedIntervalRefinementMapEventAtDefault 10 ef)))

private theorem BishopLocatedIntervalRefinementMapTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BishopLocatedIntervalRefinementMapUp,
      bishopLocatedIntervalRefinementMapFromEventFlow
          (bishopLocatedIntervalRefinementMapToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I J R D W S E H C P N =>
      change
        some
            (BishopLocatedIntervalRefinementMapUp.mk
              (bishopLocatedIntervalRefinementMapDecodeBHist
                (bishopLocatedIntervalRefinementMapEncodeBHist I))
              (bishopLocatedIntervalRefinementMapDecodeBHist
                (bishopLocatedIntervalRefinementMapEncodeBHist J))
              (bishopLocatedIntervalRefinementMapDecodeBHist
                (bishopLocatedIntervalRefinementMapEncodeBHist R))
              (bishopLocatedIntervalRefinementMapDecodeBHist
                (bishopLocatedIntervalRefinementMapEncodeBHist D))
              (bishopLocatedIntervalRefinementMapDecodeBHist
                (bishopLocatedIntervalRefinementMapEncodeBHist W))
              (bishopLocatedIntervalRefinementMapDecodeBHist
                (bishopLocatedIntervalRefinementMapEncodeBHist S))
              (bishopLocatedIntervalRefinementMapDecodeBHist
                (bishopLocatedIntervalRefinementMapEncodeBHist E))
              (bishopLocatedIntervalRefinementMapDecodeBHist
                (bishopLocatedIntervalRefinementMapEncodeBHist H))
              (bishopLocatedIntervalRefinementMapDecodeBHist
                (bishopLocatedIntervalRefinementMapEncodeBHist C))
              (bishopLocatedIntervalRefinementMapDecodeBHist
                (bishopLocatedIntervalRefinementMapEncodeBHist P))
              (bishopLocatedIntervalRefinementMapDecodeBHist
                (bishopLocatedIntervalRefinementMapEncodeBHist N))) =
          some (BishopLocatedIntervalRefinementMapUp.mk I J R D W S E H C P N)
      rw [BishopLocatedIntervalRefinementMapTasteGate_single_carrier_alignment_decode I,
        BishopLocatedIntervalRefinementMapTasteGate_single_carrier_alignment_decode J,
        BishopLocatedIntervalRefinementMapTasteGate_single_carrier_alignment_decode R,
        BishopLocatedIntervalRefinementMapTasteGate_single_carrier_alignment_decode D,
        BishopLocatedIntervalRefinementMapTasteGate_single_carrier_alignment_decode W,
        BishopLocatedIntervalRefinementMapTasteGate_single_carrier_alignment_decode S,
        BishopLocatedIntervalRefinementMapTasteGate_single_carrier_alignment_decode E,
        BishopLocatedIntervalRefinementMapTasteGate_single_carrier_alignment_decode H,
        BishopLocatedIntervalRefinementMapTasteGate_single_carrier_alignment_decode C,
        BishopLocatedIntervalRefinementMapTasteGate_single_carrier_alignment_decode P,
        BishopLocatedIntervalRefinementMapTasteGate_single_carrier_alignment_decode N]

private theorem BishopLocatedIntervalRefinementMapTasteGate_single_carrier_alignment_injective
    {x y : BishopLocatedIntervalRefinementMapUp} :
    bishopLocatedIntervalRefinementMapToEventFlow x =
        bishopLocatedIntervalRefinementMapToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopLocatedIntervalRefinementMapFromEventFlow
          (bishopLocatedIntervalRefinementMapToEventFlow x) =
        bishopLocatedIntervalRefinementMapFromEventFlow
          (bishopLocatedIntervalRefinementMapToEventFlow y) :=
    congrArg bishopLocatedIntervalRefinementMapFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BishopLocatedIntervalRefinementMapTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopLocatedIntervalRefinementMapTasteGate_single_carrier_alignment_round_trip y)))

instance bishopLocatedIntervalRefinementMapBHistCarrier :
    BHistCarrier BishopLocatedIntervalRefinementMapUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopLocatedIntervalRefinementMapToEventFlow
  fromEventFlow := bishopLocatedIntervalRefinementMapFromEventFlow

instance bishopLocatedIntervalRefinementMapChapterTasteGate :
    ChapterTasteGate BishopLocatedIntervalRefinementMapUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopLocatedIntervalRefinementMapFromEventFlow
          (bishopLocatedIntervalRefinementMapToEventFlow x) = some x
    exact BishopLocatedIntervalRefinementMapTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (BishopLocatedIntervalRefinementMapTasteGate_single_carrier_alignment_injective heq)

theorem BishopLocatedIntervalRefinementMapTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      bishopLocatedIntervalRefinementMapDecodeBHist
          (bishopLocatedIntervalRefinementMapEncodeBHist h) = h) ∧
      (∀ x : BishopLocatedIntervalRefinementMapUp,
        bishopLocatedIntervalRefinementMapFromEventFlow
            (bishopLocatedIntervalRefinementMapToEventFlow x) = some x) ∧
        (∀ x y : BishopLocatedIntervalRefinementMapUp,
          bishopLocatedIntervalRefinementMapToEventFlow x =
              bishopLocatedIntervalRefinementMapToEventFlow y →
            x = y) ∧
          bishopLocatedIntervalRefinementMapEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨BishopLocatedIntervalRefinementMapTasteGate_single_carrier_alignment_decode,
      ⟨BishopLocatedIntervalRefinementMapTasteGate_single_carrier_alignment_round_trip,
        ⟨fun _ _ heq =>
          BishopLocatedIntervalRefinementMapTasteGate_single_carrier_alignment_injective heq,
          rfl⟩⟩⟩

end BEDC.Derived.BishopLocatedIntervalRefinementMapUp
