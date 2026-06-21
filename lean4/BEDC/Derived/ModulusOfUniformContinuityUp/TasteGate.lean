import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ModulusOfUniformContinuityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ModulusOfUniformContinuityUp : Type where
  | mk (X Y F D S E H C P N : BHist) : ModulusOfUniformContinuityUp
  deriving DecidableEq

def modulusOfUniformContinuityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: modulusOfUniformContinuityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: modulusOfUniformContinuityEncodeBHist h

def modulusOfUniformContinuityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (modulusOfUniformContinuityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (modulusOfUniformContinuityDecodeBHist tail)

private theorem ModulusOfUniformContinuityTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      modulusOfUniformContinuityDecodeBHist
        (modulusOfUniformContinuityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def modulusOfUniformContinuityToEventFlow :
    ModulusOfUniformContinuityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ModulusOfUniformContinuityUp.mk X Y F D S E H C P N =>
      [[BMark.b0],
        modulusOfUniformContinuityEncodeBHist X,
        [BMark.b1, BMark.b0],
        modulusOfUniformContinuityEncodeBHist Y,
        [BMark.b1, BMark.b1, BMark.b0],
        modulusOfUniformContinuityEncodeBHist F,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        modulusOfUniformContinuityEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        modulusOfUniformContinuityEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        modulusOfUniformContinuityEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        modulusOfUniformContinuityEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        modulusOfUniformContinuityEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        modulusOfUniformContinuityEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        modulusOfUniformContinuityEncodeBHist N]

private def modulusOfUniformContinuityEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => modulusOfUniformContinuityEventAtDefault index rest

def modulusOfUniformContinuityFromEventFlow
    (ef : EventFlow) : Option ModulusOfUniformContinuityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ModulusOfUniformContinuityUp.mk
      (modulusOfUniformContinuityDecodeBHist
        (modulusOfUniformContinuityEventAtDefault 1 ef))
      (modulusOfUniformContinuityDecodeBHist
        (modulusOfUniformContinuityEventAtDefault 3 ef))
      (modulusOfUniformContinuityDecodeBHist
        (modulusOfUniformContinuityEventAtDefault 5 ef))
      (modulusOfUniformContinuityDecodeBHist
        (modulusOfUniformContinuityEventAtDefault 7 ef))
      (modulusOfUniformContinuityDecodeBHist
        (modulusOfUniformContinuityEventAtDefault 9 ef))
      (modulusOfUniformContinuityDecodeBHist
        (modulusOfUniformContinuityEventAtDefault 11 ef))
      (modulusOfUniformContinuityDecodeBHist
        (modulusOfUniformContinuityEventAtDefault 13 ef))
      (modulusOfUniformContinuityDecodeBHist
        (modulusOfUniformContinuityEventAtDefault 15 ef))
      (modulusOfUniformContinuityDecodeBHist
        (modulusOfUniformContinuityEventAtDefault 17 ef))
      (modulusOfUniformContinuityDecodeBHist
        (modulusOfUniformContinuityEventAtDefault 19 ef)))

private theorem ModulusOfUniformContinuityTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ModulusOfUniformContinuityUp,
      modulusOfUniformContinuityFromEventFlow
        (modulusOfUniformContinuityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Y F D S E H C P N =>
      change
        some
          (ModulusOfUniformContinuityUp.mk
            (modulusOfUniformContinuityDecodeBHist
              (modulusOfUniformContinuityEncodeBHist X))
            (modulusOfUniformContinuityDecodeBHist
              (modulusOfUniformContinuityEncodeBHist Y))
            (modulusOfUniformContinuityDecodeBHist
              (modulusOfUniformContinuityEncodeBHist F))
            (modulusOfUniformContinuityDecodeBHist
              (modulusOfUniformContinuityEncodeBHist D))
            (modulusOfUniformContinuityDecodeBHist
              (modulusOfUniformContinuityEncodeBHist S))
            (modulusOfUniformContinuityDecodeBHist
              (modulusOfUniformContinuityEncodeBHist E))
            (modulusOfUniformContinuityDecodeBHist
              (modulusOfUniformContinuityEncodeBHist H))
            (modulusOfUniformContinuityDecodeBHist
              (modulusOfUniformContinuityEncodeBHist C))
            (modulusOfUniformContinuityDecodeBHist
              (modulusOfUniformContinuityEncodeBHist P))
            (modulusOfUniformContinuityDecodeBHist
              (modulusOfUniformContinuityEncodeBHist N))) =
          some (ModulusOfUniformContinuityUp.mk X Y F D S E H C P N)
      rw [ModulusOfUniformContinuityTasteGate_single_carrier_alignment_decode_encode X,
        ModulusOfUniformContinuityTasteGate_single_carrier_alignment_decode_encode Y,
        ModulusOfUniformContinuityTasteGate_single_carrier_alignment_decode_encode F,
        ModulusOfUniformContinuityTasteGate_single_carrier_alignment_decode_encode D,
        ModulusOfUniformContinuityTasteGate_single_carrier_alignment_decode_encode S,
        ModulusOfUniformContinuityTasteGate_single_carrier_alignment_decode_encode E,
        ModulusOfUniformContinuityTasteGate_single_carrier_alignment_decode_encode H,
        ModulusOfUniformContinuityTasteGate_single_carrier_alignment_decode_encode C,
        ModulusOfUniformContinuityTasteGate_single_carrier_alignment_decode_encode P,
        ModulusOfUniformContinuityTasteGate_single_carrier_alignment_decode_encode N]

private theorem ModulusOfUniformContinuityTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ModulusOfUniformContinuityUp} :
    modulusOfUniformContinuityToEventFlow x =
      modulusOfUniformContinuityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      modulusOfUniformContinuityFromEventFlow (modulusOfUniformContinuityToEventFlow x) =
        modulusOfUniformContinuityFromEventFlow (modulusOfUniformContinuityToEventFlow y) :=
    congrArg modulusOfUniformContinuityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ModulusOfUniformContinuityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ModulusOfUniformContinuityTasteGate_single_carrier_alignment_round_trip y)))

def modulusOfUniformContinuityFields : ModulusOfUniformContinuityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ModulusOfUniformContinuityUp.mk X Y F D S E H C P N => [X, Y, F, D, S, E, H, C, P, N]

private theorem ModulusOfUniformContinuityTasteGate_single_carrier_alignment_fields :
    ∀ x y : ModulusOfUniformContinuityUp,
      modulusOfUniformContinuityFields x = modulusOfUniformContinuityFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 Y1 F1 D1 S1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk X2 Y2 F2 D2 S2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance modulusOfUniformContinuityBHistCarrier :
    BHistCarrier ModulusOfUniformContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := modulusOfUniformContinuityToEventFlow
  fromEventFlow := modulusOfUniformContinuityFromEventFlow

instance modulusOfUniformContinuityChapterTasteGate :
    ChapterTasteGate ModulusOfUniformContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      modulusOfUniformContinuityFromEventFlow
        (modulusOfUniformContinuityToEventFlow x) = some x
    exact ModulusOfUniformContinuityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (ModulusOfUniformContinuityTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance modulusOfUniformContinuityFieldFaithful :
    FieldFaithful ModulusOfUniformContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := modulusOfUniformContinuityFields
  field_faithful := ModulusOfUniformContinuityTasteGate_single_carrier_alignment_fields

instance modulusOfUniformContinuityNontrivial :
    BEDC.Meta.TasteGate.Nontrivial ModulusOfUniformContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ModulusOfUniformContinuityUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ModulusOfUniformContinuityUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem ModulusOfUniformContinuityTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate ModulusOfUniformContinuityUp) ∧
      Nonempty (FieldFaithful ModulusOfUniformContinuityUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial ModulusOfUniformContinuityUp) ∧
          (∀ h : BHist,
            modulusOfUniformContinuityDecodeBHist
              (modulusOfUniformContinuityEncodeBHist h) = h) ∧
            (∀ x : ModulusOfUniformContinuityUp,
              modulusOfUniformContinuityFromEventFlow
                (modulusOfUniformContinuityToEventFlow x) = some x) ∧
              (∀ x y : ModulusOfUniformContinuityUp,
                modulusOfUniformContinuityToEventFlow x =
                  modulusOfUniformContinuityToEventFlow y → x = y) ∧
                modulusOfUniformContinuityEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨modulusOfUniformContinuityChapterTasteGate⟩,
      ⟨modulusOfUniformContinuityFieldFaithful⟩,
      ⟨modulusOfUniformContinuityNontrivial⟩,
      ModulusOfUniformContinuityTasteGate_single_carrier_alignment_decode_encode,
      ModulusOfUniformContinuityTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        ModulusOfUniformContinuityTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.ModulusOfUniformContinuityUp
