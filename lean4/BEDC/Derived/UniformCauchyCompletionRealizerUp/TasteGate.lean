import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformCauchyCompletionRealizerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

/-- Token carrier for the finite uniform Cauchy completion realizer rows. -/
inductive UniformCauchyCompletionRealizerCarrier : Type where
  | mk : (F D W R M E H C P N : BHist) → UniformCauchyCompletionRealizerCarrier
  deriving DecidableEq

def uniformCauchyCompletionRealizerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformCauchyCompletionRealizerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformCauchyCompletionRealizerEncodeBHist h

def uniformCauchyCompletionRealizerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformCauchyCompletionRealizerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformCauchyCompletionRealizerDecodeBHist tail)

private theorem uniformCauchyCompletionRealizer_decode_encode :
    ∀ h : BHist,
      uniformCauchyCompletionRealizerDecodeBHist
          (uniformCauchyCompletionRealizerEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def uniformCauchyCompletionRealizerFields :
    UniformCauchyCompletionRealizerCarrier → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformCauchyCompletionRealizerCarrier.mk F D W R M E H C P N =>
      [F, D, W, R, M, E, H, C, P, N]

def uniformCauchyCompletionRealizerToEventFlow :
    UniformCauchyCompletionRealizerCarrier → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (uniformCauchyCompletionRealizerFields x).map
    uniformCauchyCompletionRealizerEncodeBHist

private def uniformCauchyCompletionRealizerEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      uniformCauchyCompletionRealizerEventAtDefault index rest

def uniformCauchyCompletionRealizerFromEventFlow
    (ef : EventFlow) : Option UniformCauchyCompletionRealizerCarrier :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (UniformCauchyCompletionRealizerCarrier.mk
      (uniformCauchyCompletionRealizerDecodeBHist
        (uniformCauchyCompletionRealizerEventAtDefault 0 ef))
      (uniformCauchyCompletionRealizerDecodeBHist
        (uniformCauchyCompletionRealizerEventAtDefault 1 ef))
      (uniformCauchyCompletionRealizerDecodeBHist
        (uniformCauchyCompletionRealizerEventAtDefault 2 ef))
      (uniformCauchyCompletionRealizerDecodeBHist
        (uniformCauchyCompletionRealizerEventAtDefault 3 ef))
      (uniformCauchyCompletionRealizerDecodeBHist
        (uniformCauchyCompletionRealizerEventAtDefault 4 ef))
      (uniformCauchyCompletionRealizerDecodeBHist
        (uniformCauchyCompletionRealizerEventAtDefault 5 ef))
      (uniformCauchyCompletionRealizerDecodeBHist
        (uniformCauchyCompletionRealizerEventAtDefault 6 ef))
      (uniformCauchyCompletionRealizerDecodeBHist
        (uniformCauchyCompletionRealizerEventAtDefault 7 ef))
      (uniformCauchyCompletionRealizerDecodeBHist
        (uniformCauchyCompletionRealizerEventAtDefault 8 ef))
      (uniformCauchyCompletionRealizerDecodeBHist
        (uniformCauchyCompletionRealizerEventAtDefault 9 ef)))

private theorem uniformCauchyCompletionRealizer_round_trip :
    ∀ x : UniformCauchyCompletionRealizerCarrier,
      uniformCauchyCompletionRealizerFromEventFlow
          (uniformCauchyCompletionRealizerToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F D W R M E H C P N =>
      change
        some
            (UniformCauchyCompletionRealizerCarrier.mk
              (uniformCauchyCompletionRealizerDecodeBHist
                (uniformCauchyCompletionRealizerEncodeBHist F))
              (uniformCauchyCompletionRealizerDecodeBHist
                (uniformCauchyCompletionRealizerEncodeBHist D))
              (uniformCauchyCompletionRealizerDecodeBHist
                (uniformCauchyCompletionRealizerEncodeBHist W))
              (uniformCauchyCompletionRealizerDecodeBHist
                (uniformCauchyCompletionRealizerEncodeBHist R))
              (uniformCauchyCompletionRealizerDecodeBHist
                (uniformCauchyCompletionRealizerEncodeBHist M))
              (uniformCauchyCompletionRealizerDecodeBHist
                (uniformCauchyCompletionRealizerEncodeBHist E))
              (uniformCauchyCompletionRealizerDecodeBHist
                (uniformCauchyCompletionRealizerEncodeBHist H))
              (uniformCauchyCompletionRealizerDecodeBHist
                (uniformCauchyCompletionRealizerEncodeBHist C))
              (uniformCauchyCompletionRealizerDecodeBHist
                (uniformCauchyCompletionRealizerEncodeBHist P))
              (uniformCauchyCompletionRealizerDecodeBHist
                (uniformCauchyCompletionRealizerEncodeBHist N))) =
          some (UniformCauchyCompletionRealizerCarrier.mk F D W R M E H C P N)
      rw [uniformCauchyCompletionRealizer_decode_encode F,
        uniformCauchyCompletionRealizer_decode_encode D,
        uniformCauchyCompletionRealizer_decode_encode W,
        uniformCauchyCompletionRealizer_decode_encode R,
        uniformCauchyCompletionRealizer_decode_encode M,
        uniformCauchyCompletionRealizer_decode_encode E,
        uniformCauchyCompletionRealizer_decode_encode H,
        uniformCauchyCompletionRealizer_decode_encode C,
        uniformCauchyCompletionRealizer_decode_encode P,
        uniformCauchyCompletionRealizer_decode_encode N]

private theorem uniformCauchyCompletionRealizerToEventFlow_injective
    {x y : UniformCauchyCompletionRealizerCarrier} :
    uniformCauchyCompletionRealizerToEventFlow x =
        uniformCauchyCompletionRealizerToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformCauchyCompletionRealizerFromEventFlow
          (uniformCauchyCompletionRealizerToEventFlow x) =
        uniformCauchyCompletionRealizerFromEventFlow
          (uniformCauchyCompletionRealizerToEventFlow y) :=
    congrArg uniformCauchyCompletionRealizerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (uniformCauchyCompletionRealizer_round_trip x).symm
      (Eq.trans hread (uniformCauchyCompletionRealizer_round_trip y)))

private theorem uniformCauchyCompletionRealizerFields_faithful :
    ∀ x y : UniformCauchyCompletionRealizerCarrier,
      uniformCauchyCompletionRealizerFields x =
          uniformCauchyCompletionRealizerFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F D W R M E H C P N =>
      cases y with
      | mk F' D' W' R' M' E' H' C' P' N' =>
          cases hfields
          rfl

instance uniformCauchyCompletionRealizerBHistCarrier :
    BHistCarrier UniformCauchyCompletionRealizerCarrier where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformCauchyCompletionRealizerToEventFlow
  fromEventFlow := uniformCauchyCompletionRealizerFromEventFlow

instance uniformCauchyCompletionRealizerChapterTasteGate :
    ChapterTasteGate UniformCauchyCompletionRealizerCarrier where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      uniformCauchyCompletionRealizerFromEventFlow
          (uniformCauchyCompletionRealizerToEventFlow x) =
        some x
    exact uniformCauchyCompletionRealizer_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (uniformCauchyCompletionRealizerToEventFlow_injective heq)

instance uniformCauchyCompletionRealizerFieldFaithful :
    FieldFaithful UniformCauchyCompletionRealizerCarrier where
  -- BEDC touchpoint anchor: BHist BMark
  fields := uniformCauchyCompletionRealizerFields
  field_faithful := uniformCauchyCompletionRealizerFields_faithful

instance uniformCauchyCompletionRealizerNontrivial :
    BEDC.Meta.TasteGate.Nontrivial UniformCauchyCompletionRealizerCarrier where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨UniformCauchyCompletionRealizerCarrier.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      UniformCauchyCompletionRealizerCarrier.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate UniformCauchyCompletionRealizerCarrier :=
  -- BEDC touchpoint anchor: BHist BMark
  uniformCauchyCompletionRealizerChapterTasteGate

theorem UniformCauchyCompletionRealizerTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        uniformCauchyCompletionRealizerDecodeBHist
            (uniformCauchyCompletionRealizerEncodeBHist h) =
          h) ∧
      (∀ x : UniformCauchyCompletionRealizerCarrier,
        uniformCauchyCompletionRealizerFromEventFlow
            (uniformCauchyCompletionRealizerToEventFlow x) =
          some x) ∧
        (∀ x y : UniformCauchyCompletionRealizerCarrier,
          uniformCauchyCompletionRealizerToEventFlow x =
              uniformCauchyCompletionRealizerToEventFlow y ->
            x = y) ∧
          uniformCauchyCompletionRealizerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier ChapterTasteGate FieldFaithful
  constructor
  · exact uniformCauchyCompletionRealizer_decode_encode
  constructor
  · exact uniformCauchyCompletionRealizer_round_trip
  constructor
  · intro x y heq
    exact uniformCauchyCompletionRealizerToEventFlow_injective heq
  · rfl

end BEDC.Derived.UniformCauchyCompletionRealizerUp
