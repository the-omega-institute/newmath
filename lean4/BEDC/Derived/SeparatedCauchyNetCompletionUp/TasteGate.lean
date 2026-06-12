import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SeparatedCauchyNetCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SeparatedCauchyNetCompletionUp : Type where
  | mk (C M Q L W R A H K P N : BHist) : SeparatedCauchyNetCompletionUp
  deriving DecidableEq

def separatedCauchyNetCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: separatedCauchyNetCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: separatedCauchyNetCompletionEncodeBHist h

def separatedCauchyNetCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (separatedCauchyNetCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (separatedCauchyNetCompletionDecodeBHist tail)

private theorem SeparatedCauchyNetCompletionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      separatedCauchyNetCompletionDecodeBHist
        (separatedCauchyNetCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def separatedCauchyNetCompletionFields :
    SeparatedCauchyNetCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SeparatedCauchyNetCompletionUp.mk C M Q L W R A H K P N =>
      [C, M, Q, L, W, R, A, H, K, P, N]

def separatedCauchyNetCompletionToEventFlow :
    SeparatedCauchyNetCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (separatedCauchyNetCompletionFields x).map
      separatedCauchyNetCompletionEncodeBHist

private def separatedCauchyNetCompletionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => separatedCauchyNetCompletionEventAt index rest

def separatedCauchyNetCompletionFromEventFlow :
    EventFlow → Option SeparatedCauchyNetCompletionUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      some
        (SeparatedCauchyNetCompletionUp.mk
          (separatedCauchyNetCompletionDecodeBHist
            (separatedCauchyNetCompletionEventAt 0 flow))
          (separatedCauchyNetCompletionDecodeBHist
            (separatedCauchyNetCompletionEventAt 1 flow))
          (separatedCauchyNetCompletionDecodeBHist
            (separatedCauchyNetCompletionEventAt 2 flow))
          (separatedCauchyNetCompletionDecodeBHist
            (separatedCauchyNetCompletionEventAt 3 flow))
          (separatedCauchyNetCompletionDecodeBHist
            (separatedCauchyNetCompletionEventAt 4 flow))
          (separatedCauchyNetCompletionDecodeBHist
            (separatedCauchyNetCompletionEventAt 5 flow))
          (separatedCauchyNetCompletionDecodeBHist
            (separatedCauchyNetCompletionEventAt 6 flow))
          (separatedCauchyNetCompletionDecodeBHist
            (separatedCauchyNetCompletionEventAt 7 flow))
          (separatedCauchyNetCompletionDecodeBHist
            (separatedCauchyNetCompletionEventAt 8 flow))
          (separatedCauchyNetCompletionDecodeBHist
            (separatedCauchyNetCompletionEventAt 9 flow))
          (separatedCauchyNetCompletionDecodeBHist
            (separatedCauchyNetCompletionEventAt 10 flow)))

private theorem SeparatedCauchyNetCompletionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : SeparatedCauchyNetCompletionUp,
      separatedCauchyNetCompletionFromEventFlow
        (separatedCauchyNetCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk C M Q L W R A H K P N =>
      change
        some
          (SeparatedCauchyNetCompletionUp.mk
            (separatedCauchyNetCompletionDecodeBHist
              (separatedCauchyNetCompletionEncodeBHist C))
            (separatedCauchyNetCompletionDecodeBHist
              (separatedCauchyNetCompletionEncodeBHist M))
            (separatedCauchyNetCompletionDecodeBHist
              (separatedCauchyNetCompletionEncodeBHist Q))
            (separatedCauchyNetCompletionDecodeBHist
              (separatedCauchyNetCompletionEncodeBHist L))
            (separatedCauchyNetCompletionDecodeBHist
              (separatedCauchyNetCompletionEncodeBHist W))
            (separatedCauchyNetCompletionDecodeBHist
              (separatedCauchyNetCompletionEncodeBHist R))
            (separatedCauchyNetCompletionDecodeBHist
              (separatedCauchyNetCompletionEncodeBHist A))
            (separatedCauchyNetCompletionDecodeBHist
              (separatedCauchyNetCompletionEncodeBHist H))
            (separatedCauchyNetCompletionDecodeBHist
              (separatedCauchyNetCompletionEncodeBHist K))
            (separatedCauchyNetCompletionDecodeBHist
              (separatedCauchyNetCompletionEncodeBHist P))
            (separatedCauchyNetCompletionDecodeBHist
              (separatedCauchyNetCompletionEncodeBHist N))) =
          some (SeparatedCauchyNetCompletionUp.mk C M Q L W R A H K P N)
      rw [SeparatedCauchyNetCompletionTasteGate_single_carrier_alignment_decode C,
        SeparatedCauchyNetCompletionTasteGate_single_carrier_alignment_decode M,
        SeparatedCauchyNetCompletionTasteGate_single_carrier_alignment_decode Q,
        SeparatedCauchyNetCompletionTasteGate_single_carrier_alignment_decode L,
        SeparatedCauchyNetCompletionTasteGate_single_carrier_alignment_decode W,
        SeparatedCauchyNetCompletionTasteGate_single_carrier_alignment_decode R,
        SeparatedCauchyNetCompletionTasteGate_single_carrier_alignment_decode A,
        SeparatedCauchyNetCompletionTasteGate_single_carrier_alignment_decode H,
        SeparatedCauchyNetCompletionTasteGate_single_carrier_alignment_decode K,
        SeparatedCauchyNetCompletionTasteGate_single_carrier_alignment_decode P,
        SeparatedCauchyNetCompletionTasteGate_single_carrier_alignment_decode N]

private theorem SeparatedCauchyNetCompletionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SeparatedCauchyNetCompletionUp} :
    separatedCauchyNetCompletionToEventFlow x =
        separatedCauchyNetCompletionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      separatedCauchyNetCompletionFromEventFlow
          (separatedCauchyNetCompletionToEventFlow x) =
        separatedCauchyNetCompletionFromEventFlow
          (separatedCauchyNetCompletionToEventFlow y) :=
    congrArg separatedCauchyNetCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (SeparatedCauchyNetCompletionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (SeparatedCauchyNetCompletionTasteGate_single_carrier_alignment_round_trip y)))

instance separatedCauchyNetCompletionBHistCarrier :
    BHistCarrier SeparatedCauchyNetCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := separatedCauchyNetCompletionToEventFlow
  fromEventFlow := separatedCauchyNetCompletionFromEventFlow

instance separatedCauchyNetCompletionChapterTasteGate :
    ChapterTasteGate SeparatedCauchyNetCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      separatedCauchyNetCompletionFromEventFlow
        (separatedCauchyNetCompletionToEventFlow x) = some x
    exact SeparatedCauchyNetCompletionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (SeparatedCauchyNetCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem SeparatedCauchyNetCompletionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      separatedCauchyNetCompletionDecodeBHist
        (separatedCauchyNetCompletionEncodeBHist h) = h) ∧
      (∀ x : SeparatedCauchyNetCompletionUp,
        separatedCauchyNetCompletionFromEventFlow
          (separatedCauchyNetCompletionToEventFlow x) = some x) ∧
        (∀ x y : SeparatedCauchyNetCompletionUp,
          separatedCauchyNetCompletionToEventFlow x =
              separatedCauchyNetCompletionToEventFlow y →
            x = y) ∧
          separatedCauchyNetCompletionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact SeparatedCauchyNetCompletionTasteGate_single_carrier_alignment_decode
  · constructor
    · exact SeparatedCauchyNetCompletionTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact SeparatedCauchyNetCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq
      · rfl

end BEDC.Derived.SeparatedCauchyNetCompletionUp
