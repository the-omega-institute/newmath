import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformCompletionReflectorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformCompletionReflectorUp : Type where
  | mk (X W Y J Q H C P N : BHist) : UniformCompletionReflectorUp
  deriving DecidableEq

def UniformCompletionReflectorTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h =>
      BMark.b0 :: UniformCompletionReflectorTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h =>
      BMark.b1 :: UniformCompletionReflectorTasteGate_single_carrier_alignment_encodeBHist h

def UniformCompletionReflectorTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0
        (UniformCompletionReflectorTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1
        (UniformCompletionReflectorTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem UniformCompletionReflectorTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      UniformCompletionReflectorTasteGate_single_carrier_alignment_decodeBHist
        (UniformCompletionReflectorTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def UniformCompletionReflectorTasteGate_single_carrier_alignment_fields :
    UniformCompletionReflectorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformCompletionReflectorUp.mk X W Y J Q H C P N => [X, W, Y, J, Q, H, C, P, N]

def UniformCompletionReflectorTasteGate_single_carrier_alignment_toEventFlow :
    UniformCompletionReflectorUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (UniformCompletionReflectorTasteGate_single_carrier_alignment_fields x).map
      UniformCompletionReflectorTasteGate_single_carrier_alignment_encodeBHist

private def UniformCompletionReflectorTasteGate_single_carrier_alignment_eventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      UniformCompletionReflectorTasteGate_single_carrier_alignment_eventAtDefault index rest

def UniformCompletionReflectorTasteGate_single_carrier_alignment_fromEventFlow
    (ef : EventFlow) : Option UniformCompletionReflectorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (UniformCompletionReflectorUp.mk
      (UniformCompletionReflectorTasteGate_single_carrier_alignment_decodeBHist
        (UniformCompletionReflectorTasteGate_single_carrier_alignment_eventAtDefault 0 ef))
      (UniformCompletionReflectorTasteGate_single_carrier_alignment_decodeBHist
        (UniformCompletionReflectorTasteGate_single_carrier_alignment_eventAtDefault 1 ef))
      (UniformCompletionReflectorTasteGate_single_carrier_alignment_decodeBHist
        (UniformCompletionReflectorTasteGate_single_carrier_alignment_eventAtDefault 2 ef))
      (UniformCompletionReflectorTasteGate_single_carrier_alignment_decodeBHist
        (UniformCompletionReflectorTasteGate_single_carrier_alignment_eventAtDefault 3 ef))
      (UniformCompletionReflectorTasteGate_single_carrier_alignment_decodeBHist
        (UniformCompletionReflectorTasteGate_single_carrier_alignment_eventAtDefault 4 ef))
      (UniformCompletionReflectorTasteGate_single_carrier_alignment_decodeBHist
        (UniformCompletionReflectorTasteGate_single_carrier_alignment_eventAtDefault 5 ef))
      (UniformCompletionReflectorTasteGate_single_carrier_alignment_decodeBHist
        (UniformCompletionReflectorTasteGate_single_carrier_alignment_eventAtDefault 6 ef))
      (UniformCompletionReflectorTasteGate_single_carrier_alignment_decodeBHist
        (UniformCompletionReflectorTasteGate_single_carrier_alignment_eventAtDefault 7 ef))
      (UniformCompletionReflectorTasteGate_single_carrier_alignment_decodeBHist
        (UniformCompletionReflectorTasteGate_single_carrier_alignment_eventAtDefault 8 ef)))

private theorem UniformCompletionReflectorTasteGate_single_carrier_alignment_round_trip :
    ∀ x : UniformCompletionReflectorUp,
      UniformCompletionReflectorTasteGate_single_carrier_alignment_fromEventFlow
        (UniformCompletionReflectorTasteGate_single_carrier_alignment_toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X W Y J Q H C P N =>
      change
        some
          (UniformCompletionReflectorUp.mk
            (UniformCompletionReflectorTasteGate_single_carrier_alignment_decodeBHist
              (UniformCompletionReflectorTasteGate_single_carrier_alignment_encodeBHist X))
            (UniformCompletionReflectorTasteGate_single_carrier_alignment_decodeBHist
              (UniformCompletionReflectorTasteGate_single_carrier_alignment_encodeBHist W))
            (UniformCompletionReflectorTasteGate_single_carrier_alignment_decodeBHist
              (UniformCompletionReflectorTasteGate_single_carrier_alignment_encodeBHist Y))
            (UniformCompletionReflectorTasteGate_single_carrier_alignment_decodeBHist
              (UniformCompletionReflectorTasteGate_single_carrier_alignment_encodeBHist J))
            (UniformCompletionReflectorTasteGate_single_carrier_alignment_decodeBHist
              (UniformCompletionReflectorTasteGate_single_carrier_alignment_encodeBHist Q))
            (UniformCompletionReflectorTasteGate_single_carrier_alignment_decodeBHist
              (UniformCompletionReflectorTasteGate_single_carrier_alignment_encodeBHist H))
            (UniformCompletionReflectorTasteGate_single_carrier_alignment_decodeBHist
              (UniformCompletionReflectorTasteGate_single_carrier_alignment_encodeBHist C))
            (UniformCompletionReflectorTasteGate_single_carrier_alignment_decodeBHist
              (UniformCompletionReflectorTasteGate_single_carrier_alignment_encodeBHist P))
            (UniformCompletionReflectorTasteGate_single_carrier_alignment_decodeBHist
              (UniformCompletionReflectorTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (UniformCompletionReflectorUp.mk X W Y J Q H C P N)
      rw [UniformCompletionReflectorTasteGate_single_carrier_alignment_decode X,
        UniformCompletionReflectorTasteGate_single_carrier_alignment_decode W,
        UniformCompletionReflectorTasteGate_single_carrier_alignment_decode Y,
        UniformCompletionReflectorTasteGate_single_carrier_alignment_decode J,
        UniformCompletionReflectorTasteGate_single_carrier_alignment_decode Q,
        UniformCompletionReflectorTasteGate_single_carrier_alignment_decode H,
        UniformCompletionReflectorTasteGate_single_carrier_alignment_decode C,
        UniformCompletionReflectorTasteGate_single_carrier_alignment_decode P,
        UniformCompletionReflectorTasteGate_single_carrier_alignment_decode N]

private theorem UniformCompletionReflectorTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : UniformCompletionReflectorUp} :
    UniformCompletionReflectorTasteGate_single_carrier_alignment_toEventFlow x =
      UniformCompletionReflectorTasteGate_single_carrier_alignment_toEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      UniformCompletionReflectorTasteGate_single_carrier_alignment_fromEventFlow
          (UniformCompletionReflectorTasteGate_single_carrier_alignment_toEventFlow x) =
        UniformCompletionReflectorTasteGate_single_carrier_alignment_fromEventFlow
          (UniformCompletionReflectorTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg UniformCompletionReflectorTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (UniformCompletionReflectorTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (UniformCompletionReflectorTasteGate_single_carrier_alignment_round_trip y)))

private theorem UniformCompletionReflectorTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : UniformCompletionReflectorUp,
      UniformCompletionReflectorTasteGate_single_carrier_alignment_fields x =
        UniformCompletionReflectorTasteGate_single_carrier_alignment_fields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X W Y J Q H C P N =>
      cases y with
      | mk X' W' Y' J' Q' H' C' P' N' =>
          cases hfields
          rfl

instance uniformCompletionReflectorBHistCarrier :
    BHistCarrier UniformCompletionReflectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := UniformCompletionReflectorTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := UniformCompletionReflectorTasteGate_single_carrier_alignment_fromEventFlow

instance uniformCompletionReflectorChapterTasteGate :
    ChapterTasteGate UniformCompletionReflectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      UniformCompletionReflectorTasteGate_single_carrier_alignment_fromEventFlow
        (UniformCompletionReflectorTasteGate_single_carrier_alignment_toEventFlow x) = some x
    exact UniformCompletionReflectorTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (UniformCompletionReflectorTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance uniformCompletionReflectorFieldFaithful :
    FieldFaithful UniformCompletionReflectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := UniformCompletionReflectorTasteGate_single_carrier_alignment_fields
  field_faithful := UniformCompletionReflectorTasteGate_single_carrier_alignment_fields_faithful

instance uniformCompletionReflectorNontrivial :
    BEDC.Meta.TasteGate.Nontrivial UniformCompletionReflectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨UniformCompletionReflectorUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      UniformCompletionReflectorUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem UniformCompletionReflectorTasteGate_single_carrier_alignment
    {X W Y J Q H C P N : BHist} :
    (fun ef => UniformCompletionReflectorTasteGate_single_carrier_alignment_fromEventFlow ef)
        (UniformCompletionReflectorTasteGate_single_carrier_alignment_toEventFlow
          (UniformCompletionReflectorUp.mk X W Y J Q H C P N)) =
      some (UniformCompletionReflectorUp.mk X W Y J Q H C P N) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    UniformCompletionReflectorTasteGate_single_carrier_alignment_round_trip
      (UniformCompletionReflectorUp.mk X W Y J Q H C P N)

end BEDC.Derived.UniformCompletionReflectorUp
