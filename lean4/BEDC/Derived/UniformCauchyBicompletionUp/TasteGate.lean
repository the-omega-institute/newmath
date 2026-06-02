import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformCauchyBicompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformCauchyBicompletionUp : Type where
  | mk (U L R J S E A H C P N : BHist) : UniformCauchyBicompletionUp
  deriving DecidableEq

def uniformCauchyBicompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformCauchyBicompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformCauchyBicompletionEncodeBHist h

def uniformCauchyBicompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformCauchyBicompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformCauchyBicompletionDecodeBHist tail)

private theorem uniformCauchyBicompletion_decode_encode :
    ∀ h : BHist,
      uniformCauchyBicompletionDecodeBHist
          (uniformCauchyBicompletionEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def uniformCauchyBicompletionFields :
    UniformCauchyBicompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformCauchyBicompletionUp.mk U L R J S E A H C P N =>
      [U, L, R, J, S, E, A, H, C, P, N]

def uniformCauchyBicompletionToEventFlow :
    UniformCauchyBicompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (uniformCauchyBicompletionFields x).map uniformCauchyBicompletionEncodeBHist

private def uniformCauchyBicompletionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => uniformCauchyBicompletionEventAt index rest

def uniformCauchyBicompletionFromEventFlow
    (ef : EventFlow) : Option UniformCauchyBicompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (UniformCauchyBicompletionUp.mk
      (uniformCauchyBicompletionDecodeBHist (uniformCauchyBicompletionEventAt 0 ef))
      (uniformCauchyBicompletionDecodeBHist (uniformCauchyBicompletionEventAt 1 ef))
      (uniformCauchyBicompletionDecodeBHist (uniformCauchyBicompletionEventAt 2 ef))
      (uniformCauchyBicompletionDecodeBHist (uniformCauchyBicompletionEventAt 3 ef))
      (uniformCauchyBicompletionDecodeBHist (uniformCauchyBicompletionEventAt 4 ef))
      (uniformCauchyBicompletionDecodeBHist (uniformCauchyBicompletionEventAt 5 ef))
      (uniformCauchyBicompletionDecodeBHist (uniformCauchyBicompletionEventAt 6 ef))
      (uniformCauchyBicompletionDecodeBHist (uniformCauchyBicompletionEventAt 7 ef))
      (uniformCauchyBicompletionDecodeBHist (uniformCauchyBicompletionEventAt 8 ef))
      (uniformCauchyBicompletionDecodeBHist (uniformCauchyBicompletionEventAt 9 ef))
      (uniformCauchyBicompletionDecodeBHist (uniformCauchyBicompletionEventAt 10 ef)))

private theorem uniformCauchyBicompletion_round_trip
    (x : UniformCauchyBicompletionUp) :
    uniformCauchyBicompletionFromEventFlow
        (uniformCauchyBicompletionToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk U L R J S E A H C P N =>
      change
        some
          (UniformCauchyBicompletionUp.mk
            (uniformCauchyBicompletionDecodeBHist
              (uniformCauchyBicompletionEncodeBHist U))
            (uniformCauchyBicompletionDecodeBHist
              (uniformCauchyBicompletionEncodeBHist L))
            (uniformCauchyBicompletionDecodeBHist
              (uniformCauchyBicompletionEncodeBHist R))
            (uniformCauchyBicompletionDecodeBHist
              (uniformCauchyBicompletionEncodeBHist J))
            (uniformCauchyBicompletionDecodeBHist
              (uniformCauchyBicompletionEncodeBHist S))
            (uniformCauchyBicompletionDecodeBHist
              (uniformCauchyBicompletionEncodeBHist E))
            (uniformCauchyBicompletionDecodeBHist
              (uniformCauchyBicompletionEncodeBHist A))
            (uniformCauchyBicompletionDecodeBHist
              (uniformCauchyBicompletionEncodeBHist H))
            (uniformCauchyBicompletionDecodeBHist
              (uniformCauchyBicompletionEncodeBHist C))
            (uniformCauchyBicompletionDecodeBHist
              (uniformCauchyBicompletionEncodeBHist P))
            (uniformCauchyBicompletionDecodeBHist
              (uniformCauchyBicompletionEncodeBHist N))) =
          some (UniformCauchyBicompletionUp.mk U L R J S E A H C P N)
      rw [uniformCauchyBicompletion_decode_encode U,
        uniformCauchyBicompletion_decode_encode L,
        uniformCauchyBicompletion_decode_encode R,
        uniformCauchyBicompletion_decode_encode J,
        uniformCauchyBicompletion_decode_encode S,
        uniformCauchyBicompletion_decode_encode E,
        uniformCauchyBicompletion_decode_encode A,
        uniformCauchyBicompletion_decode_encode H,
        uniformCauchyBicompletion_decode_encode C,
        uniformCauchyBicompletion_decode_encode P,
        uniformCauchyBicompletion_decode_encode N]

private theorem uniformCauchyBicompletionToEventFlow_injective
    {x y : UniformCauchyBicompletionUp} :
    uniformCauchyBicompletionToEventFlow x =
        uniformCauchyBicompletionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformCauchyBicompletionFromEventFlow
          (uniformCauchyBicompletionToEventFlow x) =
        uniformCauchyBicompletionFromEventFlow
          (uniformCauchyBicompletionToEventFlow y) :=
    congrArg uniformCauchyBicompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (uniformCauchyBicompletion_round_trip x).symm
      (Eq.trans hread (uniformCauchyBicompletion_round_trip y)))

instance uniformCauchyBicompletionBHistCarrier :
    BHistCarrier UniformCauchyBicompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformCauchyBicompletionToEventFlow
  fromEventFlow := uniformCauchyBicompletionFromEventFlow

instance uniformCauchyBicompletionChapterTasteGate :
    ChapterTasteGate UniformCauchyBicompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change uniformCauchyBicompletionFromEventFlow
      (uniformCauchyBicompletionToEventFlow x) = some x
    exact uniformCauchyBicompletion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (uniformCauchyBicompletionToEventFlow_injective heq)

theorem UniformCauchyBicompletionTasteGate_single_carrier_alignment :
    ChapterTasteGate UniformCauchyBicompletionUp := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact uniformCauchyBicompletionChapterTasteGate

end BEDC.Derived.UniformCauchyBicompletionUp
