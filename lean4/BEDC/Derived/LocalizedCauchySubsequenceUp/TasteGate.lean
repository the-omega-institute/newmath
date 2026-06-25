import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocalizedCauchySubsequenceUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocalizedCauchySubsequenceUp : Type where
  | mk (W S R D B E H C P N : BHist) : LocalizedCauchySubsequenceUp
  deriving DecidableEq

def localizedCauchySubsequenceFields : LocalizedCauchySubsequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocalizedCauchySubsequenceUp.mk W S R D B E H C P N => [W, S, R, D, B, E, H, C, P, N]

def localizedCauchySubsequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: localizedCauchySubsequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: localizedCauchySubsequenceEncodeBHist h

def localizedCauchySubsequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (localizedCauchySubsequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (localizedCauchySubsequenceDecodeBHist tail)

private theorem localizedCauchySubsequence_decode_encode :
    ∀ h : BHist,
      localizedCauchySubsequenceDecodeBHist
          (localizedCauchySubsequenceEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def localizedCauchySubsequenceToEventFlow :
    LocalizedCauchySubsequenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (localizedCauchySubsequenceFields x).map localizedCauchySubsequenceEncodeBHist

private def localizedCauchySubsequenceEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => localizedCauchySubsequenceEventAt index rest

def localizedCauchySubsequenceFromEventFlow
    (ef : EventFlow) : Option LocalizedCauchySubsequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocalizedCauchySubsequenceUp.mk
      (localizedCauchySubsequenceDecodeBHist (localizedCauchySubsequenceEventAt 0 ef))
      (localizedCauchySubsequenceDecodeBHist (localizedCauchySubsequenceEventAt 1 ef))
      (localizedCauchySubsequenceDecodeBHist (localizedCauchySubsequenceEventAt 2 ef))
      (localizedCauchySubsequenceDecodeBHist (localizedCauchySubsequenceEventAt 3 ef))
      (localizedCauchySubsequenceDecodeBHist (localizedCauchySubsequenceEventAt 4 ef))
      (localizedCauchySubsequenceDecodeBHist (localizedCauchySubsequenceEventAt 5 ef))
      (localizedCauchySubsequenceDecodeBHist (localizedCauchySubsequenceEventAt 6 ef))
      (localizedCauchySubsequenceDecodeBHist (localizedCauchySubsequenceEventAt 7 ef))
      (localizedCauchySubsequenceDecodeBHist (localizedCauchySubsequenceEventAt 8 ef))
      (localizedCauchySubsequenceDecodeBHist (localizedCauchySubsequenceEventAt 9 ef)))

private theorem localizedCauchySubsequence_round_trip :
    ∀ x : LocalizedCauchySubsequenceUp,
      localizedCauchySubsequenceFromEventFlow
          (localizedCauchySubsequenceToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk W S R D B E H C P N =>
      change
        some
          (LocalizedCauchySubsequenceUp.mk
            (localizedCauchySubsequenceDecodeBHist
              (localizedCauchySubsequenceEncodeBHist W))
            (localizedCauchySubsequenceDecodeBHist
              (localizedCauchySubsequenceEncodeBHist S))
            (localizedCauchySubsequenceDecodeBHist
              (localizedCauchySubsequenceEncodeBHist R))
            (localizedCauchySubsequenceDecodeBHist
              (localizedCauchySubsequenceEncodeBHist D))
            (localizedCauchySubsequenceDecodeBHist
              (localizedCauchySubsequenceEncodeBHist B))
            (localizedCauchySubsequenceDecodeBHist
              (localizedCauchySubsequenceEncodeBHist E))
            (localizedCauchySubsequenceDecodeBHist
              (localizedCauchySubsequenceEncodeBHist H))
            (localizedCauchySubsequenceDecodeBHist
              (localizedCauchySubsequenceEncodeBHist C))
            (localizedCauchySubsequenceDecodeBHist
              (localizedCauchySubsequenceEncodeBHist P))
            (localizedCauchySubsequenceDecodeBHist
              (localizedCauchySubsequenceEncodeBHist N))) =
          some (LocalizedCauchySubsequenceUp.mk W S R D B E H C P N)
      rw [localizedCauchySubsequence_decode_encode W,
        localizedCauchySubsequence_decode_encode S,
        localizedCauchySubsequence_decode_encode R,
        localizedCauchySubsequence_decode_encode D,
        localizedCauchySubsequence_decode_encode B,
        localizedCauchySubsequence_decode_encode E,
        localizedCauchySubsequence_decode_encode H,
        localizedCauchySubsequence_decode_encode C,
        localizedCauchySubsequence_decode_encode P,
        localizedCauchySubsequence_decode_encode N]

private theorem localizedCauchySubsequenceToEventFlow_injective
    {x y : LocalizedCauchySubsequenceUp} :
    localizedCauchySubsequenceToEventFlow x =
        localizedCauchySubsequenceToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      localizedCauchySubsequenceFromEventFlow
          (localizedCauchySubsequenceToEventFlow x) =
        localizedCauchySubsequenceFromEventFlow
          (localizedCauchySubsequenceToEventFlow y) :=
    congrArg localizedCauchySubsequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (localizedCauchySubsequence_round_trip x).symm
      (Eq.trans hread (localizedCauchySubsequence_round_trip y)))

instance localizedCauchySubsequenceBHistCarrier :
    BHistCarrier LocalizedCauchySubsequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := localizedCauchySubsequenceToEventFlow
  fromEventFlow := localizedCauchySubsequenceFromEventFlow

instance localizedCauchySubsequenceChapterTasteGate :
    ChapterTasteGate LocalizedCauchySubsequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      localizedCauchySubsequenceFromEventFlow
          (localizedCauchySubsequenceToEventFlow x) =
        some x
    exact localizedCauchySubsequence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (localizedCauchySubsequenceToEventFlow_injective heq)

theorem LocalizedCauchySubsequenceTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate LocalizedCauchySubsequenceUp) ∧
      Nonempty (BHistCarrier LocalizedCauchySubsequenceUp) ∧
        (∀ h : BHist,
          localizedCauchySubsequenceDecodeBHist
              (localizedCauchySubsequenceEncodeBHist h) =
            h) ∧
          (∀ x : LocalizedCauchySubsequenceUp,
            localizedCauchySubsequenceFromEventFlow
                (localizedCauchySubsequenceToEventFlow x) =
              some x) ∧
            localizedCauchySubsequenceEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨localizedCauchySubsequenceChapterTasteGate⟩,
      ⟨localizedCauchySubsequenceBHistCarrier⟩,
      localizedCauchySubsequence_decode_encode,
      localizedCauchySubsequence_round_trip,
      rfl⟩

end BEDC.Derived.LocalizedCauchySubsequenceUp.TasteGate
