import BEDC.Derived.FreeMonoidUp
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FreeMonoidUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FreeMonoidUp : Type where
  | mk (spine length payload endpoint route provenance : BHist) : FreeMonoidUp
  deriving DecidableEq

def freeMonoidEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: freeMonoidEncodeBHist h
  | BHist.e1 h => BMark.b1 :: freeMonoidEncodeBHist h

def freeMonoidDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (freeMonoidDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (freeMonoidDecodeBHist tail)

private theorem FreeMonoidTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, freeMonoidDecodeBHist (freeMonoidEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def freeMonoidFields : FreeMonoidUp → List BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | FreeMonoidUp.mk spine length payload endpoint route provenance =>
      [spine, length, payload, endpoint, route, provenance]

def freeMonoidToEventFlow : FreeMonoidUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (freeMonoidFields x).map freeMonoidEncodeBHist

def freeMonoidFromEventFlow : EventFlow → Option FreeMonoidUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | spine :: rest0 =>
      match rest0 with
      | [] => none
      | length :: rest1 =>
          match rest1 with
          | [] => none
          | payload :: rest2 =>
              match rest2 with
              | [] => none
              | endpoint :: rest3 =>
                  match rest3 with
                  | [] => none
                  | route :: rest4 =>
                      match rest4 with
                      | [] => none
                      | provenance :: rest5 =>
                          match rest5 with
                          | [] =>
                              some
                                (FreeMonoidUp.mk
                                  (freeMonoidDecodeBHist spine)
                                  (freeMonoidDecodeBHist length)
                                  (freeMonoidDecodeBHist payload)
                                  (freeMonoidDecodeBHist endpoint)
                                  (freeMonoidDecodeBHist route)
                                  (freeMonoidDecodeBHist provenance))
                          | _ :: _ => none

private theorem FreeMonoidTasteGate_single_carrier_alignment_round_trip :
    ∀ x : FreeMonoidUp, freeMonoidFromEventFlow (freeMonoidToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk spine length payload endpoint route provenance =>
      change
        some
          (FreeMonoidUp.mk
            (freeMonoidDecodeBHist (freeMonoidEncodeBHist spine))
            (freeMonoidDecodeBHist (freeMonoidEncodeBHist length))
            (freeMonoidDecodeBHist (freeMonoidEncodeBHist payload))
            (freeMonoidDecodeBHist (freeMonoidEncodeBHist endpoint))
            (freeMonoidDecodeBHist (freeMonoidEncodeBHist route))
            (freeMonoidDecodeBHist (freeMonoidEncodeBHist provenance))) =
          some (FreeMonoidUp.mk spine length payload endpoint route provenance)
      rw [FreeMonoidTasteGate_single_carrier_alignment_decode_encode spine,
        FreeMonoidTasteGate_single_carrier_alignment_decode_encode length,
        FreeMonoidTasteGate_single_carrier_alignment_decode_encode payload,
        FreeMonoidTasteGate_single_carrier_alignment_decode_encode endpoint,
        FreeMonoidTasteGate_single_carrier_alignment_decode_encode route,
        FreeMonoidTasteGate_single_carrier_alignment_decode_encode provenance]

private theorem FreeMonoidTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FreeMonoidUp} :
    freeMonoidToEventFlow x = freeMonoidToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have optionEq : some x = some y := by
    calc
      some x = freeMonoidFromEventFlow (freeMonoidToEventFlow x) :=
        (FreeMonoidTasteGate_single_carrier_alignment_round_trip x).symm
      _ = freeMonoidFromEventFlow (freeMonoidToEventFlow y) :=
        congrArg freeMonoidFromEventFlow heq
      _ = some y := FreeMonoidTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

private theorem FreeMonoidTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : FreeMonoidUp, freeMonoidFields x = freeMonoidFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk spine₁ length₁ payload₁ endpoint₁ route₁ provenance₁ =>
      cases y with
      | mk spine₂ length₂ payload₂ endpoint₂ route₂ provenance₂ =>
          injection hfields with hspine tail0
          injection tail0 with hlength tail1
          injection tail1 with hpayload tail2
          injection tail2 with hendpoint tail3
          injection tail3 with hroute tail4
          injection tail4 with hprovenance _
          subst hspine
          subst hlength
          subst hpayload
          subst hendpoint
          subst hroute
          subst hprovenance
          rfl

instance freeMonoidBHistCarrier : BHistCarrier FreeMonoidUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := freeMonoidToEventFlow
  fromEventFlow := freeMonoidFromEventFlow

instance freeMonoidChapterTasteGate : ChapterTasteGate FreeMonoidUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change freeMonoidFromEventFlow (freeMonoidToEventFlow x) = some x
    exact FreeMonoidTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FreeMonoidTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance freeMonoidFieldFaithful : FieldFaithful FreeMonoidUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := freeMonoidFields
  field_faithful := FreeMonoidTasteGate_single_carrier_alignment_field_faithful

instance freeMonoidNontrivial : Nontrivial FreeMonoidUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FreeMonoidUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FreeMonoidUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FreeMonoidUp :=
  -- BEDC touchpoint anchor: BHist BMark
  freeMonoidChapterTasteGate

theorem FreeMonoidTasteGate_single_carrier_alignment :
    (∀ h : BHist, freeMonoidDecodeBHist (freeMonoidEncodeBHist h) = h) ∧
      (∀ x : FreeMonoidUp, freeMonoidFromEventFlow (freeMonoidToEventFlow x) = some x) ∧
        (∀ x y : FreeMonoidUp, freeMonoidToEventFlow x = freeMonoidToEventFlow y → x = y) ∧
          freeMonoidEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · exact FreeMonoidTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact FreeMonoidTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact FreeMonoidTasteGate_single_carrier_alignment_toEventFlow_injective heq
      · rfl

end BEDC.Derived.FreeMonoidUp
