import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletionUniversalPropertyUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCompletionUniversalPropertyUp : Type where
  | mk (D K T F E L H C P N : BHist) : CauchyCompletionUniversalPropertyUp
  deriving DecidableEq

def cauchyCompletionUniversalPropertyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompletionUniversalPropertyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompletionUniversalPropertyEncodeBHist h

def cauchyCompletionUniversalPropertyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCompletionUniversalPropertyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCompletionUniversalPropertyDecodeBHist tail)

private theorem CauchyCompletionUniversalPropertyTasteGate_decode_encode :
    ∀ h : BHist,
      cauchyCompletionUniversalPropertyDecodeBHist
          (cauchyCompletionUniversalPropertyEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyCompletionUniversalPropertyFields :
    CauchyCompletionUniversalPropertyUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompletionUniversalPropertyUp.mk D K T F E L H C P N =>
      [D, K, T, F, E, L, H, C, P, N]

def cauchyCompletionUniversalPropertyToEventFlow :
    CauchyCompletionUniversalPropertyUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (cauchyCompletionUniversalPropertyFields x).map
      cauchyCompletionUniversalPropertyEncodeBHist

def cauchyCompletionUniversalPropertyFromEventFlow :
    EventFlow → Option CauchyCompletionUniversalPropertyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | D :: K :: T :: F :: E :: L :: H :: C :: P :: N :: [] =>
      some
        (CauchyCompletionUniversalPropertyUp.mk
          (cauchyCompletionUniversalPropertyDecodeBHist D)
          (cauchyCompletionUniversalPropertyDecodeBHist K)
          (cauchyCompletionUniversalPropertyDecodeBHist T)
          (cauchyCompletionUniversalPropertyDecodeBHist F)
          (cauchyCompletionUniversalPropertyDecodeBHist E)
          (cauchyCompletionUniversalPropertyDecodeBHist L)
          (cauchyCompletionUniversalPropertyDecodeBHist H)
          (cauchyCompletionUniversalPropertyDecodeBHist C)
          (cauchyCompletionUniversalPropertyDecodeBHist P)
          (cauchyCompletionUniversalPropertyDecodeBHist N))
  | _ => none

private theorem CauchyCompletionUniversalPropertyTasteGate_round_trip :
    ∀ x : CauchyCompletionUniversalPropertyUp,
      cauchyCompletionUniversalPropertyFromEventFlow
          (cauchyCompletionUniversalPropertyToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D K T F E L H C P N =>
      simp only [cauchyCompletionUniversalPropertyToEventFlow,
        cauchyCompletionUniversalPropertyFields,
        cauchyCompletionUniversalPropertyFromEventFlow, List.map_cons, List.map_nil,
        CauchyCompletionUniversalPropertyTasteGate_decode_encode]

private theorem CauchyCompletionUniversalPropertyTasteGate_toEventFlow_injective
    {x y : CauchyCompletionUniversalPropertyUp} :
    cauchyCompletionUniversalPropertyToEventFlow x =
        cauchyCompletionUniversalPropertyToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          cauchyCompletionUniversalPropertyFromEventFlow
            (cauchyCompletionUniversalPropertyToEventFlow x) :=
        (CauchyCompletionUniversalPropertyTasteGate_round_trip x).symm
      _ =
          cauchyCompletionUniversalPropertyFromEventFlow
            (cauchyCompletionUniversalPropertyToEventFlow y) :=
        congrArg cauchyCompletionUniversalPropertyFromEventFlow hxy
      _ = some y := CauchyCompletionUniversalPropertyTasteGate_round_trip y
  exact Option.some.inj optionEq

private theorem CauchyCompletionUniversalPropertyTasteGate_fields_faithful
    {x y : CauchyCompletionUniversalPropertyUp} :
    cauchyCompletionUniversalPropertyFields x =
        cauchyCompletionUniversalPropertyFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  cases x with
  | mk D1 K1 T1 F1 E1 L1 H1 C1 P1 N1 =>
      cases y with
      | mk D2 K2 T2 F2 E2 L2 H2 C2 P2 N2 =>
          cases h
          rfl

instance cauchyCompletionUniversalPropertyBHistCarrier :
    BHistCarrier CauchyCompletionUniversalPropertyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCompletionUniversalPropertyToEventFlow
  fromEventFlow := cauchyCompletionUniversalPropertyFromEventFlow

instance cauchyCompletionUniversalPropertyChapterTasteGate :
    ChapterTasteGate CauchyCompletionUniversalPropertyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyCompletionUniversalPropertyFromEventFlow
          (cauchyCompletionUniversalPropertyToEventFlow x) =
        some x
    exact CauchyCompletionUniversalPropertyTasteGate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyCompletionUniversalPropertyTasteGate_toEventFlow_injective heq)

instance cauchyCompletionUniversalPropertyFieldFaithful :
    FieldFaithful CauchyCompletionUniversalPropertyUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyCompletionUniversalPropertyFields
  field_faithful := by
    intro x y h
    exact CauchyCompletionUniversalPropertyTasteGate_fields_faithful h

def taste_gate : ChapterTasteGate CauchyCompletionUniversalPropertyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyCompletionUniversalPropertyChapterTasteGate

theorem CauchyCompletionUniversalPropertyTasteGate_single_carrier_alignment :
    (∀ D K T F E L H C P N : BHist,
      cauchyCompletionUniversalPropertyFields
          (CauchyCompletionUniversalPropertyUp.mk D K T F E L H C P N) =
        [D, K, T, F, E, L, H, C, P, N]) ∧
      cauchyCompletionUniversalPropertyEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  exact ⟨(fun _ _ _ _ _ _ _ _ _ _ => rfl), rfl⟩

end BEDC.Derived.CauchyCompletionUniversalPropertyUp.TasteGate
