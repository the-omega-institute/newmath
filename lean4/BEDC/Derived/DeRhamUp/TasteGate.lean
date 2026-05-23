import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DeRhamUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DeRhamUp : Type where
  | mk : (manifold tensor cochain zero form provenance : BHist) → DeRhamUp
  deriving DecidableEq

def deRhamEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: deRhamEncodeBHist h
  | BHist.e1 h => BMark.b1 :: deRhamEncodeBHist h

def deRhamDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (deRhamDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (deRhamDecodeBHist tail)

private theorem DeRhamTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, deRhamDecodeBHist (deRhamEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def DeRhamTasteGate_single_carrier_alignment_fields : DeRhamUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DeRhamUp.mk manifold tensor cochain zero form provenance =>
      [manifold, tensor, cochain, zero, form, provenance]

def deRhamToEventFlow : DeRhamUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (DeRhamTasteGate_single_carrier_alignment_fields x).map deRhamEncodeBHist

def deRhamFromEventFlow : EventFlow → Option DeRhamUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | manifold :: rest0 =>
      match rest0 with
      | [] => none
      | tensor :: rest1 =>
          match rest1 with
          | [] => none
          | cochain :: rest2 =>
              match rest2 with
              | [] => none
              | zero :: rest3 =>
                  match rest3 with
                  | [] => none
                  | form :: rest4 =>
                      match rest4 with
                      | [] => none
                      | provenance :: rest5 =>
                          match rest5 with
                          | [] =>
                              some
                                (DeRhamUp.mk
                                  (deRhamDecodeBHist manifold)
                                  (deRhamDecodeBHist tensor)
                                  (deRhamDecodeBHist cochain)
                                  (deRhamDecodeBHist zero)
                                  (deRhamDecodeBHist form)
                                  (deRhamDecodeBHist provenance))
                          | _ :: _ => none

private theorem DeRhamTasteGate_single_carrier_alignment_round_trip :
    ∀ x : DeRhamUp, deRhamFromEventFlow (deRhamToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk manifold tensor cochain zero form provenance =>
      change
        some
          (DeRhamUp.mk
            (deRhamDecodeBHist (deRhamEncodeBHist manifold))
            (deRhamDecodeBHist (deRhamEncodeBHist tensor))
            (deRhamDecodeBHist (deRhamEncodeBHist cochain))
            (deRhamDecodeBHist (deRhamEncodeBHist zero))
            (deRhamDecodeBHist (deRhamEncodeBHist form))
            (deRhamDecodeBHist (deRhamEncodeBHist provenance))) =
          some (DeRhamUp.mk manifold tensor cochain zero form provenance)
      rw [DeRhamTasteGate_single_carrier_alignment_decode_encode manifold,
        DeRhamTasteGate_single_carrier_alignment_decode_encode tensor,
        DeRhamTasteGate_single_carrier_alignment_decode_encode cochain,
        DeRhamTasteGate_single_carrier_alignment_decode_encode zero,
        DeRhamTasteGate_single_carrier_alignment_decode_encode form,
        DeRhamTasteGate_single_carrier_alignment_decode_encode provenance]

private theorem DeRhamTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DeRhamUp} :
    deRhamToEventFlow x = deRhamToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      deRhamFromEventFlow (deRhamToEventFlow x) =
        deRhamFromEventFlow (deRhamToEventFlow y) :=
    congrArg deRhamFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (DeRhamTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (DeRhamTasteGate_single_carrier_alignment_round_trip y)))

instance deRhamBHistCarrier : BHistCarrier DeRhamUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := deRhamToEventFlow
  fromEventFlow := deRhamFromEventFlow

instance deRhamChapterTasteGate : ChapterTasteGate DeRhamUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change deRhamFromEventFlow (deRhamToEventFlow x) = some x
    exact DeRhamTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DeRhamTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate DeRhamUp :=
  -- BEDC touchpoint anchor: BHist BMark
  deRhamChapterTasteGate

theorem DeRhamTasteGate_single_carrier_alignment :
    (∀ h : BHist, deRhamDecodeBHist (deRhamEncodeBHist h) = h) ∧
      deRhamEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact DeRhamTasteGate_single_carrier_alignment_decode_encode
  · rfl

end BEDC.Derived.DeRhamUp
