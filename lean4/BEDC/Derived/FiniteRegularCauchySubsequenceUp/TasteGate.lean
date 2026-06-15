import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteRegularCauchySubsequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteRegularCauchySubsequenceUp : Type where
  | mk (W M O R D E H C P N : BHist) : FiniteRegularCauchySubsequenceUp
  deriving DecidableEq

def finiteRegularCauchySubsequenceEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteRegularCauchySubsequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteRegularCauchySubsequenceEncodeBHist h

def finiteRegularCauchySubsequenceDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteRegularCauchySubsequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteRegularCauchySubsequenceDecodeBHist tail)

private theorem FiniteRegularCauchySubsequenceTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      finiteRegularCauchySubsequenceDecodeBHist
          (finiteRegularCauchySubsequenceEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteRegularCauchySubsequenceFields :
    FiniteRegularCauchySubsequenceUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteRegularCauchySubsequenceUp.mk W M O R D E H C P N =>
      [W, M, O, R, D, E, H, C, P, N]

def finiteRegularCauchySubsequenceToEventFlow :
    FiniteRegularCauchySubsequenceUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (finiteRegularCauchySubsequenceFields x).map finiteRegularCauchySubsequenceEncodeBHist

private def finiteRegularCauchySubsequenceEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => finiteRegularCauchySubsequenceEventAtDefault index rest

def finiteRegularCauchySubsequenceFromEventFlow
    (ef : EventFlow) : Option FiniteRegularCauchySubsequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FiniteRegularCauchySubsequenceUp.mk
      (finiteRegularCauchySubsequenceDecodeBHist
        (finiteRegularCauchySubsequenceEventAtDefault 0 ef))
      (finiteRegularCauchySubsequenceDecodeBHist
        (finiteRegularCauchySubsequenceEventAtDefault 1 ef))
      (finiteRegularCauchySubsequenceDecodeBHist
        (finiteRegularCauchySubsequenceEventAtDefault 2 ef))
      (finiteRegularCauchySubsequenceDecodeBHist
        (finiteRegularCauchySubsequenceEventAtDefault 3 ef))
      (finiteRegularCauchySubsequenceDecodeBHist
        (finiteRegularCauchySubsequenceEventAtDefault 4 ef))
      (finiteRegularCauchySubsequenceDecodeBHist
        (finiteRegularCauchySubsequenceEventAtDefault 5 ef))
      (finiteRegularCauchySubsequenceDecodeBHist
        (finiteRegularCauchySubsequenceEventAtDefault 6 ef))
      (finiteRegularCauchySubsequenceDecodeBHist
        (finiteRegularCauchySubsequenceEventAtDefault 7 ef))
      (finiteRegularCauchySubsequenceDecodeBHist
        (finiteRegularCauchySubsequenceEventAtDefault 8 ef))
      (finiteRegularCauchySubsequenceDecodeBHist
        (finiteRegularCauchySubsequenceEventAtDefault 9 ef)))

private theorem FiniteRegularCauchySubsequenceTasteGate_single_carrier_alignment_round_trip :
    forall x : FiniteRegularCauchySubsequenceUp,
      finiteRegularCauchySubsequenceFromEventFlow
          (finiteRegularCauchySubsequenceToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk W M O R D E H C P N =>
      change
        some
          (FiniteRegularCauchySubsequenceUp.mk
            (finiteRegularCauchySubsequenceDecodeBHist
              (finiteRegularCauchySubsequenceEncodeBHist W))
            (finiteRegularCauchySubsequenceDecodeBHist
              (finiteRegularCauchySubsequenceEncodeBHist M))
            (finiteRegularCauchySubsequenceDecodeBHist
              (finiteRegularCauchySubsequenceEncodeBHist O))
            (finiteRegularCauchySubsequenceDecodeBHist
              (finiteRegularCauchySubsequenceEncodeBHist R))
            (finiteRegularCauchySubsequenceDecodeBHist
              (finiteRegularCauchySubsequenceEncodeBHist D))
            (finiteRegularCauchySubsequenceDecodeBHist
              (finiteRegularCauchySubsequenceEncodeBHist E))
            (finiteRegularCauchySubsequenceDecodeBHist
              (finiteRegularCauchySubsequenceEncodeBHist H))
            (finiteRegularCauchySubsequenceDecodeBHist
              (finiteRegularCauchySubsequenceEncodeBHist C))
            (finiteRegularCauchySubsequenceDecodeBHist
              (finiteRegularCauchySubsequenceEncodeBHist P))
            (finiteRegularCauchySubsequenceDecodeBHist
              (finiteRegularCauchySubsequenceEncodeBHist N))) =
          some (FiniteRegularCauchySubsequenceUp.mk W M O R D E H C P N)
      rw [FiniteRegularCauchySubsequenceTasteGate_single_carrier_alignment_decode W,
        FiniteRegularCauchySubsequenceTasteGate_single_carrier_alignment_decode M,
        FiniteRegularCauchySubsequenceTasteGate_single_carrier_alignment_decode O,
        FiniteRegularCauchySubsequenceTasteGate_single_carrier_alignment_decode R,
        FiniteRegularCauchySubsequenceTasteGate_single_carrier_alignment_decode D,
        FiniteRegularCauchySubsequenceTasteGate_single_carrier_alignment_decode E,
        FiniteRegularCauchySubsequenceTasteGate_single_carrier_alignment_decode H,
        FiniteRegularCauchySubsequenceTasteGate_single_carrier_alignment_decode C,
        FiniteRegularCauchySubsequenceTasteGate_single_carrier_alignment_decode P,
        FiniteRegularCauchySubsequenceTasteGate_single_carrier_alignment_decode N]

private theorem FiniteRegularCauchySubsequenceTasteGate_single_carrier_alignment_injective
    {x y : FiniteRegularCauchySubsequenceUp} :
    finiteRegularCauchySubsequenceToEventFlow x =
        finiteRegularCauchySubsequenceToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteRegularCauchySubsequenceFromEventFlow
          (finiteRegularCauchySubsequenceToEventFlow x) =
        finiteRegularCauchySubsequenceFromEventFlow
          (finiteRegularCauchySubsequenceToEventFlow y) :=
    congrArg finiteRegularCauchySubsequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (FiniteRegularCauchySubsequenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (FiniteRegularCauchySubsequenceTasteGate_single_carrier_alignment_round_trip y)))

instance finiteRegularCauchySubsequenceBHistCarrier :
    BHistCarrier FiniteRegularCauchySubsequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteRegularCauchySubsequenceToEventFlow
  fromEventFlow := finiteRegularCauchySubsequenceFromEventFlow

instance finiteRegularCauchySubsequenceChapterTasteGate :
    ChapterTasteGate FiniteRegularCauchySubsequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteRegularCauchySubsequenceFromEventFlow
        (finiteRegularCauchySubsequenceToEventFlow x) = some x
    exact FiniteRegularCauchySubsequenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (FiniteRegularCauchySubsequenceTasteGate_single_carrier_alignment_injective heq)

def taste_gate : ChapterTasteGate FiniteRegularCauchySubsequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteRegularCauchySubsequenceChapterTasteGate

theorem FiniteRegularCauchySubsequenceTasteGate_single_carrier_alignment :
    ChapterTasteGate FiniteRegularCauchySubsequenceUp := by
  -- BEDC touchpoint anchor: BHist BMark
  exact finiteRegularCauchySubsequenceChapterTasteGate

end BEDC.Derived.FiniteRegularCauchySubsequenceUp
