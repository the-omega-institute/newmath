import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ComputableUniformContinuityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ComputableUniformContinuityUp : Type where
  | mk (X Y K R M W T E H C P N : BHist) : ComputableUniformContinuityUp
  deriving DecidableEq

def computableUniformContinuityEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: computableUniformContinuityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: computableUniformContinuityEncodeBHist h

def computableUniformContinuityDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (computableUniformContinuityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (computableUniformContinuityDecodeBHist tail)

private theorem ComputableUniformContinuityTasteGate_single_carrier_alignment_decode_aux :
    forall h : BHist,
      computableUniformContinuityDecodeBHist
        (computableUniformContinuityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def computableUniformContinuityFields :
    ComputableUniformContinuityUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ComputableUniformContinuityUp.mk X Y K R M W T E H C P N =>
      [X, Y, K, R, M, W, T, E, H, C, P, N]

def computableUniformContinuityToEventFlow :
    ComputableUniformContinuityUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (computableUniformContinuityFields x).map computableUniformContinuityEncodeBHist

private def computableUniformContinuityEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      computableUniformContinuityEventAt index rest

def computableUniformContinuityFromEventFlow
    (ef : EventFlow) : Option ComputableUniformContinuityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ComputableUniformContinuityUp.mk
      (computableUniformContinuityDecodeBHist (computableUniformContinuityEventAt 0 ef))
      (computableUniformContinuityDecodeBHist (computableUniformContinuityEventAt 1 ef))
      (computableUniformContinuityDecodeBHist (computableUniformContinuityEventAt 2 ef))
      (computableUniformContinuityDecodeBHist (computableUniformContinuityEventAt 3 ef))
      (computableUniformContinuityDecodeBHist (computableUniformContinuityEventAt 4 ef))
      (computableUniformContinuityDecodeBHist (computableUniformContinuityEventAt 5 ef))
      (computableUniformContinuityDecodeBHist (computableUniformContinuityEventAt 6 ef))
      (computableUniformContinuityDecodeBHist (computableUniformContinuityEventAt 7 ef))
      (computableUniformContinuityDecodeBHist (computableUniformContinuityEventAt 8 ef))
      (computableUniformContinuityDecodeBHist (computableUniformContinuityEventAt 9 ef))
      (computableUniformContinuityDecodeBHist (computableUniformContinuityEventAt 10 ef))
      (computableUniformContinuityDecodeBHist (computableUniformContinuityEventAt 11 ef)))

private theorem ComputableUniformContinuityTasteGate_single_carrier_alignment_round_trip
    (x : ComputableUniformContinuityUp) :
    computableUniformContinuityFromEventFlow
      (computableUniformContinuityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X Y K R M W T E H C P N =>
      change
        some
          (ComputableUniformContinuityUp.mk
            (computableUniformContinuityDecodeBHist
              (computableUniformContinuityEncodeBHist X))
            (computableUniformContinuityDecodeBHist
              (computableUniformContinuityEncodeBHist Y))
            (computableUniformContinuityDecodeBHist
              (computableUniformContinuityEncodeBHist K))
            (computableUniformContinuityDecodeBHist
              (computableUniformContinuityEncodeBHist R))
            (computableUniformContinuityDecodeBHist
              (computableUniformContinuityEncodeBHist M))
            (computableUniformContinuityDecodeBHist
              (computableUniformContinuityEncodeBHist W))
            (computableUniformContinuityDecodeBHist
              (computableUniformContinuityEncodeBHist T))
            (computableUniformContinuityDecodeBHist
              (computableUniformContinuityEncodeBHist E))
            (computableUniformContinuityDecodeBHist
              (computableUniformContinuityEncodeBHist H))
            (computableUniformContinuityDecodeBHist
              (computableUniformContinuityEncodeBHist C))
            (computableUniformContinuityDecodeBHist
              (computableUniformContinuityEncodeBHist P))
            (computableUniformContinuityDecodeBHist
              (computableUniformContinuityEncodeBHist N))) =
          some (ComputableUniformContinuityUp.mk X Y K R M W T E H C P N)
      rw [ComputableUniformContinuityTasteGate_single_carrier_alignment_decode_aux X,
        ComputableUniformContinuityTasteGate_single_carrier_alignment_decode_aux Y,
        ComputableUniformContinuityTasteGate_single_carrier_alignment_decode_aux K,
        ComputableUniformContinuityTasteGate_single_carrier_alignment_decode_aux R,
        ComputableUniformContinuityTasteGate_single_carrier_alignment_decode_aux M,
        ComputableUniformContinuityTasteGate_single_carrier_alignment_decode_aux W,
        ComputableUniformContinuityTasteGate_single_carrier_alignment_decode_aux T,
        ComputableUniformContinuityTasteGate_single_carrier_alignment_decode_aux E,
        ComputableUniformContinuityTasteGate_single_carrier_alignment_decode_aux H,
        ComputableUniformContinuityTasteGate_single_carrier_alignment_decode_aux C,
        ComputableUniformContinuityTasteGate_single_carrier_alignment_decode_aux P,
        ComputableUniformContinuityTasteGate_single_carrier_alignment_decode_aux N]

private theorem ComputableUniformContinuityTasteGate_single_carrier_alignment_injective_aux
    {x y : ComputableUniformContinuityUp} :
    computableUniformContinuityToEventFlow x = computableUniformContinuityToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      computableUniformContinuityFromEventFlow (computableUniformContinuityToEventFlow x) =
        computableUniformContinuityFromEventFlow (computableUniformContinuityToEventFlow y) :=
    congrArg computableUniformContinuityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ComputableUniformContinuityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ComputableUniformContinuityTasteGate_single_carrier_alignment_round_trip y)))

instance computableUniformContinuityBHistCarrier :
    BHistCarrier ComputableUniformContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := computableUniformContinuityToEventFlow
  fromEventFlow := computableUniformContinuityFromEventFlow

instance computableUniformContinuityChapterTasteGate :
    ChapterTasteGate ComputableUniformContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      computableUniformContinuityFromEventFlow
        (computableUniformContinuityToEventFlow x) = some x
    exact ComputableUniformContinuityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ComputableUniformContinuityTasteGate_single_carrier_alignment_injective_aux heq)

theorem ComputableUniformContinuityTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      computableUniformContinuityDecodeBHist (computableUniformContinuityEncodeBHist h) = h) ∧
      (∀ x : ComputableUniformContinuityUp,
        computableUniformContinuityFromEventFlow (computableUniformContinuityToEventFlow x) =
          some x) ∧
      (∀ x y : ComputableUniformContinuityUp,
        computableUniformContinuityToEventFlow x = computableUniformContinuityToEventFlow y ->
          x = y) ∧
      computableUniformContinuityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ComputableUniformContinuityTasteGate_single_carrier_alignment_decode_aux
  · constructor
    · exact ComputableUniformContinuityTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact ComputableUniformContinuityTasteGate_single_carrier_alignment_injective_aux heq
      · rfl

end BEDC.Derived.ComputableUniformContinuityUp
