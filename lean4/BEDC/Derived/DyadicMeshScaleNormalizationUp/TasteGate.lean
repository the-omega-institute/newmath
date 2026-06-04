import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicMeshScaleNormalizationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicMeshScaleNormalizationUp : Type where
  | mk (G A B S D T W R E H C P N : BHist) : DyadicMeshScaleNormalizationUp
  deriving DecidableEq

def dyadicMeshScaleNormalizationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicMeshScaleNormalizationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicMeshScaleNormalizationEncodeBHist h

def dyadicMeshScaleNormalizationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicMeshScaleNormalizationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicMeshScaleNormalizationDecodeBHist tail)

private theorem DyadicMeshScaleNormalizationTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      dyadicMeshScaleNormalizationDecodeBHist
          (dyadicMeshScaleNormalizationEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dyadicMeshScaleNormalizationFields :
    DyadicMeshScaleNormalizationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicMeshScaleNormalizationUp.mk G A B S D T W R E H C P N =>
      [G, A, B, S, D, T, W, R, E, H, C, P, N]

def dyadicMeshScaleNormalizationToEventFlow :
    DyadicMeshScaleNormalizationUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (dyadicMeshScaleNormalizationFields x).map
      dyadicMeshScaleNormalizationEncodeBHist

private def dyadicMeshScaleNormalizationEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      dyadicMeshScaleNormalizationEventAtDefault index rest

def dyadicMeshScaleNormalizationFromEventFlow
    (ef : EventFlow) : Option DyadicMeshScaleNormalizationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DyadicMeshScaleNormalizationUp.mk
      (dyadicMeshScaleNormalizationDecodeBHist
        (dyadicMeshScaleNormalizationEventAtDefault 0 ef))
      (dyadicMeshScaleNormalizationDecodeBHist
        (dyadicMeshScaleNormalizationEventAtDefault 1 ef))
      (dyadicMeshScaleNormalizationDecodeBHist
        (dyadicMeshScaleNormalizationEventAtDefault 2 ef))
      (dyadicMeshScaleNormalizationDecodeBHist
        (dyadicMeshScaleNormalizationEventAtDefault 3 ef))
      (dyadicMeshScaleNormalizationDecodeBHist
        (dyadicMeshScaleNormalizationEventAtDefault 4 ef))
      (dyadicMeshScaleNormalizationDecodeBHist
        (dyadicMeshScaleNormalizationEventAtDefault 5 ef))
      (dyadicMeshScaleNormalizationDecodeBHist
        (dyadicMeshScaleNormalizationEventAtDefault 6 ef))
      (dyadicMeshScaleNormalizationDecodeBHist
        (dyadicMeshScaleNormalizationEventAtDefault 7 ef))
      (dyadicMeshScaleNormalizationDecodeBHist
        (dyadicMeshScaleNormalizationEventAtDefault 8 ef))
      (dyadicMeshScaleNormalizationDecodeBHist
        (dyadicMeshScaleNormalizationEventAtDefault 9 ef))
      (dyadicMeshScaleNormalizationDecodeBHist
        (dyadicMeshScaleNormalizationEventAtDefault 10 ef))
      (dyadicMeshScaleNormalizationDecodeBHist
        (dyadicMeshScaleNormalizationEventAtDefault 11 ef))
      (dyadicMeshScaleNormalizationDecodeBHist
        (dyadicMeshScaleNormalizationEventAtDefault 12 ef)))

private theorem DyadicMeshScaleNormalizationTasteGate_single_carrier_alignment_round_trip
    (x : DyadicMeshScaleNormalizationUp) :
    dyadicMeshScaleNormalizationFromEventFlow
        (dyadicMeshScaleNormalizationToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk G A B S D T W R E H C P N =>
      change
        some
          (DyadicMeshScaleNormalizationUp.mk
            (dyadicMeshScaleNormalizationDecodeBHist
              (dyadicMeshScaleNormalizationEncodeBHist G))
            (dyadicMeshScaleNormalizationDecodeBHist
              (dyadicMeshScaleNormalizationEncodeBHist A))
            (dyadicMeshScaleNormalizationDecodeBHist
              (dyadicMeshScaleNormalizationEncodeBHist B))
            (dyadicMeshScaleNormalizationDecodeBHist
              (dyadicMeshScaleNormalizationEncodeBHist S))
            (dyadicMeshScaleNormalizationDecodeBHist
              (dyadicMeshScaleNormalizationEncodeBHist D))
            (dyadicMeshScaleNormalizationDecodeBHist
              (dyadicMeshScaleNormalizationEncodeBHist T))
            (dyadicMeshScaleNormalizationDecodeBHist
              (dyadicMeshScaleNormalizationEncodeBHist W))
            (dyadicMeshScaleNormalizationDecodeBHist
              (dyadicMeshScaleNormalizationEncodeBHist R))
            (dyadicMeshScaleNormalizationDecodeBHist
              (dyadicMeshScaleNormalizationEncodeBHist E))
            (dyadicMeshScaleNormalizationDecodeBHist
              (dyadicMeshScaleNormalizationEncodeBHist H))
            (dyadicMeshScaleNormalizationDecodeBHist
              (dyadicMeshScaleNormalizationEncodeBHist C))
            (dyadicMeshScaleNormalizationDecodeBHist
              (dyadicMeshScaleNormalizationEncodeBHist P))
            (dyadicMeshScaleNormalizationDecodeBHist
              (dyadicMeshScaleNormalizationEncodeBHist N))) =
          some (DyadicMeshScaleNormalizationUp.mk G A B S D T W R E H C P N)
      rw [DyadicMeshScaleNormalizationTasteGate_single_carrier_alignment_decode_encode G,
        DyadicMeshScaleNormalizationTasteGate_single_carrier_alignment_decode_encode A,
        DyadicMeshScaleNormalizationTasteGate_single_carrier_alignment_decode_encode B,
        DyadicMeshScaleNormalizationTasteGate_single_carrier_alignment_decode_encode S,
        DyadicMeshScaleNormalizationTasteGate_single_carrier_alignment_decode_encode D,
        DyadicMeshScaleNormalizationTasteGate_single_carrier_alignment_decode_encode T,
        DyadicMeshScaleNormalizationTasteGate_single_carrier_alignment_decode_encode W,
        DyadicMeshScaleNormalizationTasteGate_single_carrier_alignment_decode_encode R,
        DyadicMeshScaleNormalizationTasteGate_single_carrier_alignment_decode_encode E,
        DyadicMeshScaleNormalizationTasteGate_single_carrier_alignment_decode_encode H,
        DyadicMeshScaleNormalizationTasteGate_single_carrier_alignment_decode_encode C,
        DyadicMeshScaleNormalizationTasteGate_single_carrier_alignment_decode_encode P,
        DyadicMeshScaleNormalizationTasteGate_single_carrier_alignment_decode_encode N]

private theorem DyadicMeshScaleNormalizationTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DyadicMeshScaleNormalizationUp} :
    dyadicMeshScaleNormalizationToEventFlow x =
        dyadicMeshScaleNormalizationToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicMeshScaleNormalizationFromEventFlow
          (dyadicMeshScaleNormalizationToEventFlow x) =
        dyadicMeshScaleNormalizationFromEventFlow
          (dyadicMeshScaleNormalizationToEventFlow y) :=
    congrArg dyadicMeshScaleNormalizationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (DyadicMeshScaleNormalizationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (DyadicMeshScaleNormalizationTasteGate_single_carrier_alignment_round_trip y)))

instance dyadicMeshScaleNormalizationBHistCarrier :
    BHistCarrier DyadicMeshScaleNormalizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicMeshScaleNormalizationToEventFlow
  fromEventFlow := dyadicMeshScaleNormalizationFromEventFlow

instance dyadicMeshScaleNormalizationChapterTasteGate :
    ChapterTasteGate DyadicMeshScaleNormalizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      dyadicMeshScaleNormalizationFromEventFlow
          (dyadicMeshScaleNormalizationToEventFlow x) =
        some x
    exact DyadicMeshScaleNormalizationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (DyadicMeshScaleNormalizationTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

theorem DyadicMeshScaleNormalizationTasteGate_single_carrier_alignment :
    (forall h : BHist,
      dyadicMeshScaleNormalizationDecodeBHist
          (dyadicMeshScaleNormalizationEncodeBHist h) =
        h) ∧
      Nonempty (BHistCarrier DyadicMeshScaleNormalizationUp) ∧
        Nonempty (ChapterTasteGate DyadicMeshScaleNormalizationUp) ∧
          dyadicMeshScaleNormalizationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨DyadicMeshScaleNormalizationTasteGate_single_carrier_alignment_decode_encode,
      ⟨⟨dyadicMeshScaleNormalizationBHistCarrier⟩,
        ⟨⟨dyadicMeshScaleNormalizationChapterTasteGate⟩, rfl⟩⟩⟩

end BEDC.Derived.DyadicMeshScaleNormalizationUp
