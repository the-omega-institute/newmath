import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DecimalExpansionUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DecimalExpansionUp : Type where
  | mk (D W V Q R E H C P N : BHist) : DecimalExpansionUp
  deriving DecidableEq

def DecimalExpansionTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: DecimalExpansionTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: DecimalExpansionTasteGate_single_carrier_alignment_encodeBHist h

def DecimalExpansionTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0
      (DecimalExpansionTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1
      (DecimalExpansionTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem DecimalExpansionTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      DecimalExpansionTasteGate_single_carrier_alignment_decodeBHist
          (DecimalExpansionTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def DecimalExpansionTasteGate_single_carrier_alignment_fields :
    DecimalExpansionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DecimalExpansionUp.mk D W V Q R E H C P N => [D, W, V, Q, R, E, H, C, P, N]

def DecimalExpansionTasteGate_single_carrier_alignment_toEventFlow :
    DecimalExpansionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (DecimalExpansionTasteGate_single_carrier_alignment_fields x).map
      DecimalExpansionTasteGate_single_carrier_alignment_encodeBHist

def DecimalExpansionTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option DecimalExpansionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | D :: W :: V :: Q :: R :: E :: H :: C :: P :: N :: [] =>
      some
        (DecimalExpansionUp.mk
          (DecimalExpansionTasteGate_single_carrier_alignment_decodeBHist D)
          (DecimalExpansionTasteGate_single_carrier_alignment_decodeBHist W)
          (DecimalExpansionTasteGate_single_carrier_alignment_decodeBHist V)
          (DecimalExpansionTasteGate_single_carrier_alignment_decodeBHist Q)
          (DecimalExpansionTasteGate_single_carrier_alignment_decodeBHist R)
          (DecimalExpansionTasteGate_single_carrier_alignment_decodeBHist E)
          (DecimalExpansionTasteGate_single_carrier_alignment_decodeBHist H)
          (DecimalExpansionTasteGate_single_carrier_alignment_decodeBHist C)
          (DecimalExpansionTasteGate_single_carrier_alignment_decodeBHist P)
          (DecimalExpansionTasteGate_single_carrier_alignment_decodeBHist N))
  | _ => none

private theorem DecimalExpansionTasteGate_single_carrier_alignment_round_trip :
    forall x : DecimalExpansionUp,
      DecimalExpansionTasteGate_single_carrier_alignment_fromEventFlow
          (DecimalExpansionTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D W V Q R E H C P N =>
      simp only [DecimalExpansionTasteGate_single_carrier_alignment_toEventFlow,
        DecimalExpansionTasteGate_single_carrier_alignment_fields,
        DecimalExpansionTasteGate_single_carrier_alignment_fromEventFlow, List.map_cons,
        List.map_nil, DecimalExpansionTasteGate_single_carrier_alignment_decode_encode]

private theorem DecimalExpansionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DecimalExpansionUp} :
    DecimalExpansionTasteGate_single_carrier_alignment_toEventFlow x =
        DecimalExpansionTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          DecimalExpansionTasteGate_single_carrier_alignment_fromEventFlow
            (DecimalExpansionTasteGate_single_carrier_alignment_toEventFlow x) :=
        (DecimalExpansionTasteGate_single_carrier_alignment_round_trip x).symm
      _ =
          DecimalExpansionTasteGate_single_carrier_alignment_fromEventFlow
            (DecimalExpansionTasteGate_single_carrier_alignment_toEventFlow y) :=
        congrArg DecimalExpansionTasteGate_single_carrier_alignment_fromEventFlow hxy
      _ = some y := DecimalExpansionTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

instance DecimalExpansionTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier DecimalExpansionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := DecimalExpansionTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := DecimalExpansionTasteGate_single_carrier_alignment_fromEventFlow

instance DecimalExpansionTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate DecimalExpansionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      DecimalExpansionTasteGate_single_carrier_alignment_fromEventFlow
          (DecimalExpansionTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact DecimalExpansionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DecimalExpansionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem DecimalExpansionTasteGate_single_carrier_alignment :
    (forall D W V Q R E H C P N : BHist,
      DecimalExpansionTasteGate_single_carrier_alignment_fields
          (DecimalExpansionUp.mk D W V Q R E H C P N) =
        [D, W, V, Q, R, E, H, C, P, N]) ∧
      DecimalExpansionTasteGate_single_carrier_alignment_encodeBHist BHist.Empty =
        ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact ⟨(fun _ _ _ _ _ _ _ _ _ _ => rfl), rfl⟩

end BEDC.Derived.DecimalExpansionUp.TasteGate
