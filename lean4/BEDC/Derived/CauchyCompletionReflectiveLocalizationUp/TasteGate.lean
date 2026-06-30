import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletionReflectiveLocalizationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCompletionReflectiveLocalizationUp : Type where
  | mk (S Q I U F K T H C P N : BHist) : CauchyCompletionReflectiveLocalizationUp
  deriving DecidableEq

def cauchyCompletionReflectiveLocalizationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompletionReflectiveLocalizationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompletionReflectiveLocalizationEncodeBHist h

def cauchyCompletionReflectiveLocalizationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCompletionReflectiveLocalizationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCompletionReflectiveLocalizationDecodeBHist tail)

private theorem CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cauchyCompletionReflectiveLocalizationDecodeBHist
        (cauchyCompletionReflectiveLocalizationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyCompletionReflectiveLocalizationFields :
    CauchyCompletionReflectiveLocalizationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompletionReflectiveLocalizationUp.mk S Q I U F K T H C P N =>
      [S, Q, I, U, F, K, T, H, C, P, N]

def cauchyCompletionReflectiveLocalizationToEventFlow :
    CauchyCompletionReflectiveLocalizationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (cauchyCompletionReflectiveLocalizationFields x).map
        cauchyCompletionReflectiveLocalizationEncodeBHist

private def cauchyCompletionReflectiveLocalizationEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      cauchyCompletionReflectiveLocalizationEventAtDefault index rest

def cauchyCompletionReflectiveLocalizationFromEventFlow
    (ef : EventFlow) : Option CauchyCompletionReflectiveLocalizationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyCompletionReflectiveLocalizationUp.mk
      (cauchyCompletionReflectiveLocalizationDecodeBHist
        (cauchyCompletionReflectiveLocalizationEventAtDefault 0 ef))
      (cauchyCompletionReflectiveLocalizationDecodeBHist
        (cauchyCompletionReflectiveLocalizationEventAtDefault 1 ef))
      (cauchyCompletionReflectiveLocalizationDecodeBHist
        (cauchyCompletionReflectiveLocalizationEventAtDefault 2 ef))
      (cauchyCompletionReflectiveLocalizationDecodeBHist
        (cauchyCompletionReflectiveLocalizationEventAtDefault 3 ef))
      (cauchyCompletionReflectiveLocalizationDecodeBHist
        (cauchyCompletionReflectiveLocalizationEventAtDefault 4 ef))
      (cauchyCompletionReflectiveLocalizationDecodeBHist
        (cauchyCompletionReflectiveLocalizationEventAtDefault 5 ef))
      (cauchyCompletionReflectiveLocalizationDecodeBHist
        (cauchyCompletionReflectiveLocalizationEventAtDefault 6 ef))
      (cauchyCompletionReflectiveLocalizationDecodeBHist
        (cauchyCompletionReflectiveLocalizationEventAtDefault 7 ef))
      (cauchyCompletionReflectiveLocalizationDecodeBHist
        (cauchyCompletionReflectiveLocalizationEventAtDefault 8 ef))
      (cauchyCompletionReflectiveLocalizationDecodeBHist
        (cauchyCompletionReflectiveLocalizationEventAtDefault 9 ef))
      (cauchyCompletionReflectiveLocalizationDecodeBHist
        (cauchyCompletionReflectiveLocalizationEventAtDefault 10 ef)))

private theorem CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyCompletionReflectiveLocalizationUp,
      cauchyCompletionReflectiveLocalizationFromEventFlow
        (cauchyCompletionReflectiveLocalizationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S Q I U F K T H C P N =>
      change
        some
          (CauchyCompletionReflectiveLocalizationUp.mk
            (cauchyCompletionReflectiveLocalizationDecodeBHist
              (cauchyCompletionReflectiveLocalizationEncodeBHist S))
            (cauchyCompletionReflectiveLocalizationDecodeBHist
              (cauchyCompletionReflectiveLocalizationEncodeBHist Q))
            (cauchyCompletionReflectiveLocalizationDecodeBHist
              (cauchyCompletionReflectiveLocalizationEncodeBHist I))
            (cauchyCompletionReflectiveLocalizationDecodeBHist
              (cauchyCompletionReflectiveLocalizationEncodeBHist U))
            (cauchyCompletionReflectiveLocalizationDecodeBHist
              (cauchyCompletionReflectiveLocalizationEncodeBHist F))
            (cauchyCompletionReflectiveLocalizationDecodeBHist
              (cauchyCompletionReflectiveLocalizationEncodeBHist K))
            (cauchyCompletionReflectiveLocalizationDecodeBHist
              (cauchyCompletionReflectiveLocalizationEncodeBHist T))
            (cauchyCompletionReflectiveLocalizationDecodeBHist
              (cauchyCompletionReflectiveLocalizationEncodeBHist H))
            (cauchyCompletionReflectiveLocalizationDecodeBHist
              (cauchyCompletionReflectiveLocalizationEncodeBHist C))
            (cauchyCompletionReflectiveLocalizationDecodeBHist
              (cauchyCompletionReflectiveLocalizationEncodeBHist P))
            (cauchyCompletionReflectiveLocalizationDecodeBHist
              (cauchyCompletionReflectiveLocalizationEncodeBHist N))) =
          some (CauchyCompletionReflectiveLocalizationUp.mk S Q I U F K T H C P N)
      rw [
        CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_decode S,
        CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_decode Q,
        CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_decode I,
        CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_decode U,
        CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_decode F,
        CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_decode K,
        CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_decode T,
        CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_decode H,
        CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_decode C,
        CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_decode P,
        CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_decode N]

private theorem CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyCompletionReflectiveLocalizationUp} :
    cauchyCompletionReflectiveLocalizationToEventFlow x =
      cauchyCompletionReflectiveLocalizationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCompletionReflectiveLocalizationFromEventFlow
          (cauchyCompletionReflectiveLocalizationToEventFlow x) =
        cauchyCompletionReflectiveLocalizationFromEventFlow
          (cauchyCompletionReflectiveLocalizationToEventFlow y) :=
    congrArg cauchyCompletionReflectiveLocalizationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_round_trip y)))

private theorem CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_fields :
    ∀ x y : CauchyCompletionReflectiveLocalizationUp,
      cauchyCompletionReflectiveLocalizationFields x =
        cauchyCompletionReflectiveLocalizationFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 Q1 I1 U1 F1 K1 T1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 Q2 I2 U2 F2 K2 T2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance cauchyCompletionReflectiveLocalizationBHistCarrier :
    BHistCarrier CauchyCompletionReflectiveLocalizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCompletionReflectiveLocalizationToEventFlow
  fromEventFlow := cauchyCompletionReflectiveLocalizationFromEventFlow

instance cauchyCompletionReflectiveLocalizationChapterTasteGate :
    ChapterTasteGate CauchyCompletionReflectiveLocalizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyCompletionReflectiveLocalizationFromEventFlow
        (cauchyCompletionReflectiveLocalizationToEventFlow x) = some x
    exact CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

instance cauchyCompletionReflectiveLocalizationFieldFaithful :
    FieldFaithful CauchyCompletionReflectiveLocalizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyCompletionReflectiveLocalizationFields
  field_faithful :=
    CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_fields

def taste_gate : ChapterTasteGate CauchyCompletionReflectiveLocalizationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyCompletionReflectiveLocalizationChapterTasteGate

theorem CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment :
    (cauchyCompletionReflectiveLocalizationEncodeBHist BHist.Empty = ([] : RawEvent)) ∧
      (∀ h : BHist,
        cauchyCompletionReflectiveLocalizationDecodeBHist
          (cauchyCompletionReflectiveLocalizationEncodeBHist h) = h) ∧
        (∀ x : CauchyCompletionReflectiveLocalizationUp,
          cauchyCompletionReflectiveLocalizationFromEventFlow
            (cauchyCompletionReflectiveLocalizationToEventFlow x) = some x) ∧
          (∀ x y : CauchyCompletionReflectiveLocalizationUp,
            cauchyCompletionReflectiveLocalizationFields x =
              cauchyCompletionReflectiveLocalizationFields y → x = y) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  exact
    ⟨rfl,
      CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_decode,
      CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_round_trip,
      CauchyCompletionReflectiveLocalizationTasteGate_single_carrier_alignment_fields⟩

end BEDC.Derived.CauchyCompletionReflectiveLocalizationUp
