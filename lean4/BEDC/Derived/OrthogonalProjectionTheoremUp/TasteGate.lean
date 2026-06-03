import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.OrthogonalProjectionTheoremUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive OrthogonalProjectionTheoremUp : Type where
  | mk (H V I Nm B A Q R O T C P N : BHist) : OrthogonalProjectionTheoremUp
  deriving DecidableEq

def orthogonalProjectionTheoremEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: orthogonalProjectionTheoremEncodeBHist h
  | BHist.e1 h => BMark.b1 :: orthogonalProjectionTheoremEncodeBHist h

def orthogonalProjectionTheoremDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (orthogonalProjectionTheoremDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (orthogonalProjectionTheoremDecodeBHist tail)

private theorem OrthogonalProjectionTheoremTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      orthogonalProjectionTheoremDecodeBHist
          (orthogonalProjectionTheoremEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def orthogonalProjectionTheoremToEventFlow :
    OrthogonalProjectionTheoremUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | OrthogonalProjectionTheoremUp.mk H V I Nm B A Q R O T C P N =>
      [orthogonalProjectionTheoremEncodeBHist H,
        orthogonalProjectionTheoremEncodeBHist V,
        orthogonalProjectionTheoremEncodeBHist I,
        orthogonalProjectionTheoremEncodeBHist Nm,
        orthogonalProjectionTheoremEncodeBHist B,
        orthogonalProjectionTheoremEncodeBHist A,
        orthogonalProjectionTheoremEncodeBHist Q,
        orthogonalProjectionTheoremEncodeBHist R,
        orthogonalProjectionTheoremEncodeBHist O,
        orthogonalProjectionTheoremEncodeBHist T,
        orthogonalProjectionTheoremEncodeBHist C,
        orthogonalProjectionTheoremEncodeBHist P,
        orthogonalProjectionTheoremEncodeBHist N]

private def orthogonalProjectionTheoremEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => orthogonalProjectionTheoremEventAt index rest

def orthogonalProjectionTheoremDecodeFields (ef : EventFlow) :
    OrthogonalProjectionTheoremUp :=
  -- BEDC touchpoint anchor: BHist BMark
  OrthogonalProjectionTheoremUp.mk
    (orthogonalProjectionTheoremDecodeBHist (orthogonalProjectionTheoremEventAt 0 ef))
    (orthogonalProjectionTheoremDecodeBHist (orthogonalProjectionTheoremEventAt 1 ef))
    (orthogonalProjectionTheoremDecodeBHist (orthogonalProjectionTheoremEventAt 2 ef))
    (orthogonalProjectionTheoremDecodeBHist (orthogonalProjectionTheoremEventAt 3 ef))
    (orthogonalProjectionTheoremDecodeBHist (orthogonalProjectionTheoremEventAt 4 ef))
    (orthogonalProjectionTheoremDecodeBHist (orthogonalProjectionTheoremEventAt 5 ef))
    (orthogonalProjectionTheoremDecodeBHist (orthogonalProjectionTheoremEventAt 6 ef))
    (orthogonalProjectionTheoremDecodeBHist (orthogonalProjectionTheoremEventAt 7 ef))
    (orthogonalProjectionTheoremDecodeBHist (orthogonalProjectionTheoremEventAt 8 ef))
    (orthogonalProjectionTheoremDecodeBHist (orthogonalProjectionTheoremEventAt 9 ef))
    (orthogonalProjectionTheoremDecodeBHist (orthogonalProjectionTheoremEventAt 10 ef))
    (orthogonalProjectionTheoremDecodeBHist (orthogonalProjectionTheoremEventAt 11 ef))
    (orthogonalProjectionTheoremDecodeBHist (orthogonalProjectionTheoremEventAt 12 ef))

def orthogonalProjectionTheoremFromEventFlow :
    EventFlow -> Option OrthogonalProjectionTheoremUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef => some (orthogonalProjectionTheoremDecodeFields ef)

private theorem OrthogonalProjectionTheoremTasteGate_single_carrier_alignment_round_trip
    (x : OrthogonalProjectionTheoremUp) :
    orthogonalProjectionTheoremFromEventFlow
        (orthogonalProjectionTheoremToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk H V I Nm B A Q R O T C P N =>
      change
        some
            (OrthogonalProjectionTheoremUp.mk
              (orthogonalProjectionTheoremDecodeBHist
                (orthogonalProjectionTheoremEncodeBHist H))
              (orthogonalProjectionTheoremDecodeBHist
                (orthogonalProjectionTheoremEncodeBHist V))
              (orthogonalProjectionTheoremDecodeBHist
                (orthogonalProjectionTheoremEncodeBHist I))
              (orthogonalProjectionTheoremDecodeBHist
                (orthogonalProjectionTheoremEncodeBHist Nm))
              (orthogonalProjectionTheoremDecodeBHist
                (orthogonalProjectionTheoremEncodeBHist B))
              (orthogonalProjectionTheoremDecodeBHist
                (orthogonalProjectionTheoremEncodeBHist A))
              (orthogonalProjectionTheoremDecodeBHist
                (orthogonalProjectionTheoremEncodeBHist Q))
              (orthogonalProjectionTheoremDecodeBHist
                (orthogonalProjectionTheoremEncodeBHist R))
              (orthogonalProjectionTheoremDecodeBHist
                (orthogonalProjectionTheoremEncodeBHist O))
              (orthogonalProjectionTheoremDecodeBHist
                (orthogonalProjectionTheoremEncodeBHist T))
              (orthogonalProjectionTheoremDecodeBHist
                (orthogonalProjectionTheoremEncodeBHist C))
              (orthogonalProjectionTheoremDecodeBHist
                (orthogonalProjectionTheoremEncodeBHist P))
              (orthogonalProjectionTheoremDecodeBHist
                (orthogonalProjectionTheoremEncodeBHist N))) =
          some (OrthogonalProjectionTheoremUp.mk H V I Nm B A Q R O T C P N)
      rw [OrthogonalProjectionTheoremTasteGate_single_carrier_alignment_decode_encode H,
        OrthogonalProjectionTheoremTasteGate_single_carrier_alignment_decode_encode V,
        OrthogonalProjectionTheoremTasteGate_single_carrier_alignment_decode_encode I,
        OrthogonalProjectionTheoremTasteGate_single_carrier_alignment_decode_encode Nm,
        OrthogonalProjectionTheoremTasteGate_single_carrier_alignment_decode_encode B,
        OrthogonalProjectionTheoremTasteGate_single_carrier_alignment_decode_encode A,
        OrthogonalProjectionTheoremTasteGate_single_carrier_alignment_decode_encode Q,
        OrthogonalProjectionTheoremTasteGate_single_carrier_alignment_decode_encode R,
        OrthogonalProjectionTheoremTasteGate_single_carrier_alignment_decode_encode O,
        OrthogonalProjectionTheoremTasteGate_single_carrier_alignment_decode_encode T,
        OrthogonalProjectionTheoremTasteGate_single_carrier_alignment_decode_encode C,
        OrthogonalProjectionTheoremTasteGate_single_carrier_alignment_decode_encode P,
        OrthogonalProjectionTheoremTasteGate_single_carrier_alignment_decode_encode N]

private theorem OrthogonalProjectionTheoremTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : OrthogonalProjectionTheoremUp} :
    orthogonalProjectionTheoremToEventFlow x =
        orthogonalProjectionTheoremToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      orthogonalProjectionTheoremFromEventFlow
          (orthogonalProjectionTheoremToEventFlow x) =
        orthogonalProjectionTheoremFromEventFlow
          (orthogonalProjectionTheoremToEventFlow y) :=
    congrArg orthogonalProjectionTheoremFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (OrthogonalProjectionTheoremTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (OrthogonalProjectionTheoremTasteGate_single_carrier_alignment_round_trip y)))

instance orthogonalProjectionTheoremBHistCarrier :
    BHistCarrier OrthogonalProjectionTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := orthogonalProjectionTheoremToEventFlow
  fromEventFlow := orthogonalProjectionTheoremFromEventFlow

instance orthogonalProjectionTheoremChapterTasteGate :
    ChapterTasteGate OrthogonalProjectionTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      orthogonalProjectionTheoremFromEventFlow
          (orthogonalProjectionTheoremToEventFlow x) =
        some x
    exact OrthogonalProjectionTheoremTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (OrthogonalProjectionTheoremTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem OrthogonalProjectionTheoremTasteGate_single_carrier_alignment :
    (forall h : BHist,
      orthogonalProjectionTheoremDecodeBHist
          (orthogonalProjectionTheoremEncodeBHist h) =
        h) ∧
      Nonempty (BHistCarrier OrthogonalProjectionTheoremUp) ∧
        Nonempty (ChapterTasteGate OrthogonalProjectionTheoremUp) ∧
          orthogonalProjectionTheoremEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨OrthogonalProjectionTheoremTasteGate_single_carrier_alignment_decode_encode,
      ⟨orthogonalProjectionTheoremBHistCarrier⟩,
      ⟨orthogonalProjectionTheoremChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.OrthogonalProjectionTheoremUp
