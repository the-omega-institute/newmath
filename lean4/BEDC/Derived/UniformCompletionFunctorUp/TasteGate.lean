import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformCompletionFunctorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformCompletionFunctorUp : Type where
  | mk (U F E R W D S H C P N : BHist) : UniformCompletionFunctorUp
  deriving DecidableEq

def uniformCompletionFunctorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformCompletionFunctorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformCompletionFunctorEncodeBHist h

def uniformCompletionFunctorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformCompletionFunctorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformCompletionFunctorDecodeBHist tail)

private theorem UniformCompletionFunctorTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, uniformCompletionFunctorDecodeBHist
      (uniformCompletionFunctorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def uniformCompletionFunctorFields : UniformCompletionFunctorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformCompletionFunctorUp.mk U F E R W D S H C P N => [U, F, E, R, W, D, S, H, C, P, N]

def uniformCompletionFunctorToEventFlow : UniformCompletionFunctorUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (uniformCompletionFunctorFields x).map uniformCompletionFunctorEncodeBHist

private def uniformCompletionFunctorEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => uniformCompletionFunctorEventAtDefault index rest

def uniformCompletionFunctorFromEventFlow
    (ef : EventFlow) : Option UniformCompletionFunctorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (UniformCompletionFunctorUp.mk
      (uniformCompletionFunctorDecodeBHist (uniformCompletionFunctorEventAtDefault 0 ef))
      (uniformCompletionFunctorDecodeBHist (uniformCompletionFunctorEventAtDefault 1 ef))
      (uniformCompletionFunctorDecodeBHist (uniformCompletionFunctorEventAtDefault 2 ef))
      (uniformCompletionFunctorDecodeBHist (uniformCompletionFunctorEventAtDefault 3 ef))
      (uniformCompletionFunctorDecodeBHist (uniformCompletionFunctorEventAtDefault 4 ef))
      (uniformCompletionFunctorDecodeBHist (uniformCompletionFunctorEventAtDefault 5 ef))
      (uniformCompletionFunctorDecodeBHist (uniformCompletionFunctorEventAtDefault 6 ef))
      (uniformCompletionFunctorDecodeBHist (uniformCompletionFunctorEventAtDefault 7 ef))
      (uniformCompletionFunctorDecodeBHist (uniformCompletionFunctorEventAtDefault 8 ef))
      (uniformCompletionFunctorDecodeBHist (uniformCompletionFunctorEventAtDefault 9 ef))
      (uniformCompletionFunctorDecodeBHist (uniformCompletionFunctorEventAtDefault 10 ef)))

private theorem UniformCompletionFunctorTasteGate_single_carrier_alignment_round_trip :
    ∀ x : UniformCompletionFunctorUp,
      uniformCompletionFunctorFromEventFlow
        (uniformCompletionFunctorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk U F E R W D S H C P N =>
      change
        some
          (UniformCompletionFunctorUp.mk
            (uniformCompletionFunctorDecodeBHist (uniformCompletionFunctorEncodeBHist U))
            (uniformCompletionFunctorDecodeBHist (uniformCompletionFunctorEncodeBHist F))
            (uniformCompletionFunctorDecodeBHist (uniformCompletionFunctorEncodeBHist E))
            (uniformCompletionFunctorDecodeBHist (uniformCompletionFunctorEncodeBHist R))
            (uniformCompletionFunctorDecodeBHist (uniformCompletionFunctorEncodeBHist W))
            (uniformCompletionFunctorDecodeBHist (uniformCompletionFunctorEncodeBHist D))
            (uniformCompletionFunctorDecodeBHist (uniformCompletionFunctorEncodeBHist S))
            (uniformCompletionFunctorDecodeBHist (uniformCompletionFunctorEncodeBHist H))
            (uniformCompletionFunctorDecodeBHist (uniformCompletionFunctorEncodeBHist C))
            (uniformCompletionFunctorDecodeBHist (uniformCompletionFunctorEncodeBHist P))
            (uniformCompletionFunctorDecodeBHist (uniformCompletionFunctorEncodeBHist N))) =
          some (UniformCompletionFunctorUp.mk U F E R W D S H C P N)
      rw [UniformCompletionFunctorTasteGate_single_carrier_alignment_decode U,
        UniformCompletionFunctorTasteGate_single_carrier_alignment_decode F,
        UniformCompletionFunctorTasteGate_single_carrier_alignment_decode E,
        UniformCompletionFunctorTasteGate_single_carrier_alignment_decode R,
        UniformCompletionFunctorTasteGate_single_carrier_alignment_decode W,
        UniformCompletionFunctorTasteGate_single_carrier_alignment_decode D,
        UniformCompletionFunctorTasteGate_single_carrier_alignment_decode S,
        UniformCompletionFunctorTasteGate_single_carrier_alignment_decode H,
        UniformCompletionFunctorTasteGate_single_carrier_alignment_decode C,
        UniformCompletionFunctorTasteGate_single_carrier_alignment_decode P,
        UniformCompletionFunctorTasteGate_single_carrier_alignment_decode N]

private theorem UniformCompletionFunctorTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : UniformCompletionFunctorUp} :
    uniformCompletionFunctorToEventFlow x =
      uniformCompletionFunctorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformCompletionFunctorFromEventFlow (uniformCompletionFunctorToEventFlow x) =
        uniformCompletionFunctorFromEventFlow (uniformCompletionFunctorToEventFlow y) :=
    congrArg uniformCompletionFunctorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (UniformCompletionFunctorTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (UniformCompletionFunctorTasteGate_single_carrier_alignment_round_trip y)))

private theorem UniformCompletionFunctorTasteGate_single_carrier_alignment_fields :
    ∀ x y : UniformCompletionFunctorUp,
      uniformCompletionFunctorFields x = uniformCompletionFunctorFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk U1 F1 E1 R1 W1 D1 S1 H1 C1 P1 N1 =>
      cases y with
      | mk U2 F2 E2 R2 W2 D2 S2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance uniformCompletionFunctorBHistCarrier :
    BHistCarrier UniformCompletionFunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformCompletionFunctorToEventFlow
  fromEventFlow := uniformCompletionFunctorFromEventFlow

instance uniformCompletionFunctorChapterTasteGate :
    ChapterTasteGate UniformCompletionFunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      uniformCompletionFunctorFromEventFlow
        (uniformCompletionFunctorToEventFlow x) = some x
    exact UniformCompletionFunctorTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (UniformCompletionFunctorTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance uniformCompletionFunctorFieldFaithful :
    FieldFaithful UniformCompletionFunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := uniformCompletionFunctorFields
  field_faithful := UniformCompletionFunctorTasteGate_single_carrier_alignment_fields

instance uniformCompletionFunctorNontrivial :
    BEDC.Meta.TasteGate.Nontrivial UniformCompletionFunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨UniformCompletionFunctorUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      UniformCompletionFunctorUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate UniformCompletionFunctorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  uniformCompletionFunctorChapterTasteGate

theorem UniformCompletionFunctorTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate UniformCompletionFunctorUp) ∧
      Nonempty (FieldFaithful UniformCompletionFunctorUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial UniformCompletionFunctorUp) ∧
          (∀ h : BHist,
            uniformCompletionFunctorDecodeBHist (uniformCompletionFunctorEncodeBHist h) = h) ∧
            (∀ x : UniformCompletionFunctorUp,
              uniformCompletionFunctorFromEventFlow (uniformCompletionFunctorToEventFlow x) =
                some x) ∧
              (∀ x y : UniformCompletionFunctorUp,
                uniformCompletionFunctorToEventFlow x = uniformCompletionFunctorToEventFlow y →
                  x = y) ∧
                uniformCompletionFunctorEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨uniformCompletionFunctorChapterTasteGate⟩,
      ⟨uniformCompletionFunctorFieldFaithful⟩,
      ⟨uniformCompletionFunctorNontrivial⟩,
      UniformCompletionFunctorTasteGate_single_carrier_alignment_decode,
      UniformCompletionFunctorTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        UniformCompletionFunctorTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.UniformCompletionFunctorUp
