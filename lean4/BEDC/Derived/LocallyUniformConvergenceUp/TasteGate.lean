import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocallyUniformConvergenceUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocallyUniformConvergenceUp : Type where
  | mk (K U F Q E H C P N : BHist) : LocallyUniformConvergenceUp
  deriving DecidableEq

def locallyUniformConvergenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locallyUniformConvergenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locallyUniformConvergenceEncodeBHist h

def locallyUniformConvergenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locallyUniformConvergenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locallyUniformConvergenceDecodeBHist tail)

private theorem locallyUniformConvergence_decode_encode_bhist :
    ∀ h : BHist,
      locallyUniformConvergenceDecodeBHist (locallyUniformConvergenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locallyUniformConvergenceToEventFlow : LocallyUniformConvergenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LocallyUniformConvergenceUp.mk K U F Q E H C P N =>
      [locallyUniformConvergenceEncodeBHist K,
        locallyUniformConvergenceEncodeBHist U,
        locallyUniformConvergenceEncodeBHist F,
        locallyUniformConvergenceEncodeBHist Q,
        locallyUniformConvergenceEncodeBHist E,
        locallyUniformConvergenceEncodeBHist H,
        locallyUniformConvergenceEncodeBHist C,
        locallyUniformConvergenceEncodeBHist P,
        locallyUniformConvergenceEncodeBHist N]

private def locallyUniformConvergenceEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locallyUniformConvergenceEventAt index rest

def locallyUniformConvergenceFromEventFlow :
    EventFlow → Option LocallyUniformConvergenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (LocallyUniformConvergenceUp.mk
        (locallyUniformConvergenceDecodeBHist (locallyUniformConvergenceEventAt 0 ef))
        (locallyUniformConvergenceDecodeBHist (locallyUniformConvergenceEventAt 1 ef))
        (locallyUniformConvergenceDecodeBHist (locallyUniformConvergenceEventAt 2 ef))
        (locallyUniformConvergenceDecodeBHist (locallyUniformConvergenceEventAt 3 ef))
        (locallyUniformConvergenceDecodeBHist (locallyUniformConvergenceEventAt 4 ef))
        (locallyUniformConvergenceDecodeBHist (locallyUniformConvergenceEventAt 5 ef))
        (locallyUniformConvergenceDecodeBHist (locallyUniformConvergenceEventAt 6 ef))
        (locallyUniformConvergenceDecodeBHist (locallyUniformConvergenceEventAt 7 ef))
        (locallyUniformConvergenceDecodeBHist (locallyUniformConvergenceEventAt 8 ef)))

private theorem locallyUniformConvergence_round_trip :
    ∀ x : LocallyUniformConvergenceUp,
      locallyUniformConvergenceFromEventFlow
          (locallyUniformConvergenceToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K U F Q E H C P N =>
      change
        some
            (LocallyUniformConvergenceUp.mk
              (locallyUniformConvergenceDecodeBHist
                (locallyUniformConvergenceEncodeBHist K))
              (locallyUniformConvergenceDecodeBHist
                (locallyUniformConvergenceEncodeBHist U))
              (locallyUniformConvergenceDecodeBHist
                (locallyUniformConvergenceEncodeBHist F))
              (locallyUniformConvergenceDecodeBHist
                (locallyUniformConvergenceEncodeBHist Q))
              (locallyUniformConvergenceDecodeBHist
                (locallyUniformConvergenceEncodeBHist E))
              (locallyUniformConvergenceDecodeBHist
                (locallyUniformConvergenceEncodeBHist H))
              (locallyUniformConvergenceDecodeBHist
                (locallyUniformConvergenceEncodeBHist C))
              (locallyUniformConvergenceDecodeBHist
                (locallyUniformConvergenceEncodeBHist P))
              (locallyUniformConvergenceDecodeBHist
                (locallyUniformConvergenceEncodeBHist N))) =
          some (LocallyUniformConvergenceUp.mk K U F Q E H C P N)
      rw [locallyUniformConvergence_decode_encode_bhist K,
        locallyUniformConvergence_decode_encode_bhist U,
        locallyUniformConvergence_decode_encode_bhist F,
        locallyUniformConvergence_decode_encode_bhist Q,
        locallyUniformConvergence_decode_encode_bhist E,
        locallyUniformConvergence_decode_encode_bhist H,
        locallyUniformConvergence_decode_encode_bhist C,
        locallyUniformConvergence_decode_encode_bhist P,
        locallyUniformConvergence_decode_encode_bhist N]

private theorem locallyUniformConvergenceToEventFlow_injective
    {x y : LocallyUniformConvergenceUp} :
    locallyUniformConvergenceToEventFlow x =
      locallyUniformConvergenceToEventFlow y →
    x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locallyUniformConvergenceFromEventFlow
          (locallyUniformConvergenceToEventFlow x) =
        locallyUniformConvergenceFromEventFlow
          (locallyUniformConvergenceToEventFlow y) :=
    congrArg locallyUniformConvergenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (locallyUniformConvergence_round_trip x).symm
      (Eq.trans hread (locallyUniformConvergence_round_trip y)))

instance locallyUniformConvergenceBHistCarrier :
    BHistCarrier LocallyUniformConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locallyUniformConvergenceToEventFlow
  fromEventFlow := locallyUniformConvergenceFromEventFlow

instance locallyUniformConvergenceChapterTasteGate :
    ChapterTasteGate LocallyUniformConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      locallyUniformConvergenceFromEventFlow
          (locallyUniformConvergenceToEventFlow x) =
        some x
    exact locallyUniformConvergence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locallyUniformConvergenceToEventFlow_injective heq)

theorem LocallyUniformConvergenceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      locallyUniformConvergenceDecodeBHist (locallyUniformConvergenceEncodeBHist h) = h) ∧
      (∀ x : LocallyUniformConvergenceUp,
        locallyUniformConvergenceFromEventFlow
            (locallyUniformConvergenceToEventFlow x) =
          some x) ∧
        (∀ x y : LocallyUniformConvergenceUp,
          locallyUniformConvergenceToEventFlow x =
            locallyUniformConvergenceToEventFlow y →
          x = y) ∧
          locallyUniformConvergenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨locallyUniformConvergence_decode_encode_bhist,
      locallyUniformConvergence_round_trip,
      fun _x _y => locallyUniformConvergenceToEventFlow_injective,
      rfl⟩

end BEDC.Derived.LocallyUniformConvergenceUp.TasteGate
