import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MonotoneCauchySubsequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MonotoneCauchySubsequenceUp : Type where
  | mk (S I M D R E H C P N : BHist) : MonotoneCauchySubsequenceUp
  deriving DecidableEq

def monotoneCauchySubsequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: monotoneCauchySubsequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: monotoneCauchySubsequenceEncodeBHist h

def monotoneCauchySubsequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (monotoneCauchySubsequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (monotoneCauchySubsequenceDecodeBHist tail)

private theorem monotoneCauchySubsequenceDecode_encode_bhist :
    ∀ h : BHist,
      monotoneCauchySubsequenceDecodeBHist (monotoneCauchySubsequenceEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def monotoneCauchySubsequenceFields :
    MonotoneCauchySubsequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MonotoneCauchySubsequenceUp.mk S I M D R E H C P N => [S, I, M, D, R, E, H, C, P, N]

def monotoneCauchySubsequenceToEventFlow :
    MonotoneCauchySubsequenceUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (monotoneCauchySubsequenceFields x).map monotoneCauchySubsequenceEncodeBHist

private def monotoneCauchySubsequenceEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => monotoneCauchySubsequenceEventAt index rest

def monotoneCauchySubsequenceFromEventFlow
    (ef : EventFlow) : Option MonotoneCauchySubsequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MonotoneCauchySubsequenceUp.mk
      (monotoneCauchySubsequenceDecodeBHist (monotoneCauchySubsequenceEventAt 0 ef))
      (monotoneCauchySubsequenceDecodeBHist (monotoneCauchySubsequenceEventAt 1 ef))
      (monotoneCauchySubsequenceDecodeBHist (monotoneCauchySubsequenceEventAt 2 ef))
      (monotoneCauchySubsequenceDecodeBHist (monotoneCauchySubsequenceEventAt 3 ef))
      (monotoneCauchySubsequenceDecodeBHist (monotoneCauchySubsequenceEventAt 4 ef))
      (monotoneCauchySubsequenceDecodeBHist (monotoneCauchySubsequenceEventAt 5 ef))
      (monotoneCauchySubsequenceDecodeBHist (monotoneCauchySubsequenceEventAt 6 ef))
      (monotoneCauchySubsequenceDecodeBHist (monotoneCauchySubsequenceEventAt 7 ef))
      (monotoneCauchySubsequenceDecodeBHist (monotoneCauchySubsequenceEventAt 8 ef))
      (monotoneCauchySubsequenceDecodeBHist (monotoneCauchySubsequenceEventAt 9 ef)))

private theorem monotoneCauchySubsequence_round_trip
    (x : MonotoneCauchySubsequenceUp) :
    monotoneCauchySubsequenceFromEventFlow (monotoneCauchySubsequenceToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S I M D R E H C P N =>
      change
        some
          (MonotoneCauchySubsequenceUp.mk
            (monotoneCauchySubsequenceDecodeBHist (monotoneCauchySubsequenceEncodeBHist S))
            (monotoneCauchySubsequenceDecodeBHist (monotoneCauchySubsequenceEncodeBHist I))
            (monotoneCauchySubsequenceDecodeBHist (monotoneCauchySubsequenceEncodeBHist M))
            (monotoneCauchySubsequenceDecodeBHist (monotoneCauchySubsequenceEncodeBHist D))
            (monotoneCauchySubsequenceDecodeBHist (monotoneCauchySubsequenceEncodeBHist R))
            (monotoneCauchySubsequenceDecodeBHist (monotoneCauchySubsequenceEncodeBHist E))
            (monotoneCauchySubsequenceDecodeBHist (monotoneCauchySubsequenceEncodeBHist H))
            (monotoneCauchySubsequenceDecodeBHist (monotoneCauchySubsequenceEncodeBHist C))
            (monotoneCauchySubsequenceDecodeBHist (monotoneCauchySubsequenceEncodeBHist P))
            (monotoneCauchySubsequenceDecodeBHist (monotoneCauchySubsequenceEncodeBHist N))) =
          some (MonotoneCauchySubsequenceUp.mk S I M D R E H C P N)
      rw [monotoneCauchySubsequenceDecode_encode_bhist S,
        monotoneCauchySubsequenceDecode_encode_bhist I,
        monotoneCauchySubsequenceDecode_encode_bhist M,
        monotoneCauchySubsequenceDecode_encode_bhist D,
        monotoneCauchySubsequenceDecode_encode_bhist R,
        monotoneCauchySubsequenceDecode_encode_bhist E,
        monotoneCauchySubsequenceDecode_encode_bhist H,
        monotoneCauchySubsequenceDecode_encode_bhist C,
        monotoneCauchySubsequenceDecode_encode_bhist P,
        monotoneCauchySubsequenceDecode_encode_bhist N]

private theorem monotoneCauchySubsequenceToEventFlow_injective
    {x y : MonotoneCauchySubsequenceUp} :
    monotoneCauchySubsequenceToEventFlow x =
        monotoneCauchySubsequenceToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      monotoneCauchySubsequenceFromEventFlow (monotoneCauchySubsequenceToEventFlow x) =
        monotoneCauchySubsequenceFromEventFlow (monotoneCauchySubsequenceToEventFlow y) :=
    congrArg monotoneCauchySubsequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (monotoneCauchySubsequence_round_trip x).symm
      (Eq.trans hread (monotoneCauchySubsequence_round_trip y)))

instance monotoneCauchySubsequenceBHistCarrier :
    BHistCarrier MonotoneCauchySubsequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := monotoneCauchySubsequenceToEventFlow
  fromEventFlow := monotoneCauchySubsequenceFromEventFlow

instance monotoneCauchySubsequenceChapterTasteGate :
    ChapterTasteGate MonotoneCauchySubsequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      monotoneCauchySubsequenceFromEventFlow (monotoneCauchySubsequenceToEventFlow x) =
        some x
    exact monotoneCauchySubsequence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (monotoneCauchySubsequenceToEventFlow_injective heq)

theorem MonotoneCauchySubsequenceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      monotoneCauchySubsequenceDecodeBHist (monotoneCauchySubsequenceEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier MonotoneCauchySubsequenceUp) ∧
        Nonempty (ChapterTasteGate MonotoneCauchySubsequenceUp) ∧
          monotoneCauchySubsequenceEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier ChapterTasteGate
  exact
    ⟨monotoneCauchySubsequenceDecode_encode_bhist,
      ⟨monotoneCauchySubsequenceBHistCarrier⟩,
      ⟨monotoneCauchySubsequenceChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.MonotoneCauchySubsequenceUp
