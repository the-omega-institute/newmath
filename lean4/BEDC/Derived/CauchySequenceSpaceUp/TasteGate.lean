import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchySequenceSpaceUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchySequenceSpaceUp : Type where
  | mk :
      (family schedule window tolerance completion transport route name endpoint : BHist) ->
        CauchySequenceSpaceUp
  deriving DecidableEq

def cauchySequenceSpaceEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchySequenceSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchySequenceSpaceEncodeBHist h

def cauchySequenceSpaceDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchySequenceSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchySequenceSpaceDecodeBHist tail)

theorem CauchySequenceSpaceTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      cauchySequenceSpaceDecodeBHist (cauchySequenceSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cauchySequenceSpaceFields : CauchySequenceSpaceUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchySequenceSpaceUp.mk family schedule window tolerance completion transport route name
      endpoint =>
      [family, schedule, window, tolerance, completion, transport, route, name, endpoint]

def cauchySequenceSpaceToEventFlow : CauchySequenceSpaceUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchySequenceSpaceFields x).map cauchySequenceSpaceEncodeBHist

def cauchySequenceSpaceFromEventFlow : EventFlow -> Option CauchySequenceSpaceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | family :: rest0 =>
      match rest0 with
      | [] => none
      | schedule :: rest1 =>
          match rest1 with
          | [] => none
          | window :: rest2 =>
              match rest2 with
              | [] => none
              | tolerance :: rest3 =>
                  match rest3 with
                  | [] => none
                  | completion :: rest4 =>
                      match rest4 with
                      | [] => none
                      | transport :: rest5 =>
                          match rest5 with
                          | [] => none
                          | route :: rest6 =>
                              match rest6 with
                              | [] => none
                              | name :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | endpoint :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (CauchySequenceSpaceUp.mk
                                              (cauchySequenceSpaceDecodeBHist family)
                                              (cauchySequenceSpaceDecodeBHist schedule)
                                              (cauchySequenceSpaceDecodeBHist window)
                                              (cauchySequenceSpaceDecodeBHist tolerance)
                                              (cauchySequenceSpaceDecodeBHist completion)
                                              (cauchySequenceSpaceDecodeBHist transport)
                                              (cauchySequenceSpaceDecodeBHist route)
                                              (cauchySequenceSpaceDecodeBHist name)
                                              (cauchySequenceSpaceDecodeBHist endpoint))
                                      | _ :: _ => none

theorem CauchySequenceSpaceTasteGate_single_carrier_alignment_round_trip :
    forall x : CauchySequenceSpaceUp,
      cauchySequenceSpaceFromEventFlow (cauchySequenceSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk family schedule window tolerance completion transport route name endpoint =>
      change
        some
          (CauchySequenceSpaceUp.mk
            (cauchySequenceSpaceDecodeBHist (cauchySequenceSpaceEncodeBHist family))
            (cauchySequenceSpaceDecodeBHist (cauchySequenceSpaceEncodeBHist schedule))
            (cauchySequenceSpaceDecodeBHist (cauchySequenceSpaceEncodeBHist window))
            (cauchySequenceSpaceDecodeBHist (cauchySequenceSpaceEncodeBHist tolerance))
            (cauchySequenceSpaceDecodeBHist (cauchySequenceSpaceEncodeBHist completion))
            (cauchySequenceSpaceDecodeBHist (cauchySequenceSpaceEncodeBHist transport))
            (cauchySequenceSpaceDecodeBHist (cauchySequenceSpaceEncodeBHist route))
            (cauchySequenceSpaceDecodeBHist (cauchySequenceSpaceEncodeBHist name))
            (cauchySequenceSpaceDecodeBHist (cauchySequenceSpaceEncodeBHist endpoint))) =
          some
            (CauchySequenceSpaceUp.mk family schedule window tolerance completion transport route
              name endpoint)
      rw [CauchySequenceSpaceTasteGate_single_carrier_alignment_decode_encode family,
        CauchySequenceSpaceTasteGate_single_carrier_alignment_decode_encode schedule,
        CauchySequenceSpaceTasteGate_single_carrier_alignment_decode_encode window,
        CauchySequenceSpaceTasteGate_single_carrier_alignment_decode_encode tolerance,
        CauchySequenceSpaceTasteGate_single_carrier_alignment_decode_encode completion,
        CauchySequenceSpaceTasteGate_single_carrier_alignment_decode_encode transport,
        CauchySequenceSpaceTasteGate_single_carrier_alignment_decode_encode route,
        CauchySequenceSpaceTasteGate_single_carrier_alignment_decode_encode name,
        CauchySequenceSpaceTasteGate_single_carrier_alignment_decode_encode endpoint]

theorem CauchySequenceSpaceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchySequenceSpaceUp} :
    cauchySequenceSpaceToEventFlow x = cauchySequenceSpaceToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchySequenceSpaceFromEventFlow (cauchySequenceSpaceToEventFlow x) =
        cauchySequenceSpaceFromEventFlow (cauchySequenceSpaceToEventFlow y) :=
    congrArg cauchySequenceSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchySequenceSpaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CauchySequenceSpaceTasteGate_single_carrier_alignment_round_trip y)))

theorem CauchySequenceSpaceTasteGate_single_carrier_alignment_field_faithful :
    forall x y : CauchySequenceSpaceUp,
      cauchySequenceSpaceFields x = cauchySequenceSpaceFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk family₁ schedule₁ window₁ tolerance₁ completion₁ transport₁ route₁ name₁ endpoint₁ =>
      cases y with
      | mk family₂ schedule₂ window₂ tolerance₂ completion₂ transport₂ route₂ name₂ endpoint₂ =>
          cases hfields
          rfl

instance cauchySequenceSpaceBHistCarrier : BHistCarrier CauchySequenceSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchySequenceSpaceToEventFlow
  fromEventFlow := cauchySequenceSpaceFromEventFlow

instance cauchySequenceSpaceChapterTasteGate : ChapterTasteGate CauchySequenceSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := fun x =>
    id (CauchySequenceSpaceTasteGate_single_carrier_alignment_round_trip x)
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchySequenceSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance cauchySequenceSpaceFieldFaithful : FieldFaithful CauchySequenceSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchySequenceSpaceFields
  field_faithful := CauchySequenceSpaceTasteGate_single_carrier_alignment_field_faithful

instance cauchySequenceSpaceNontrivial : Nontrivial CauchySequenceSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchySequenceSpaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchySequenceSpaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchySequenceSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchySequenceSpaceChapterTasteGate

theorem CauchySequenceSpaceTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CauchySequenceSpaceUp) ∧
      Nonempty (FieldFaithful CauchySequenceSpaceUp) ∧
        Nonempty (Nontrivial CauchySequenceSpaceUp) ∧
          (∀ h : BHist,
            cauchySequenceSpaceDecodeBHist (cauchySequenceSpaceEncodeBHist h) = h) ∧
            (∀ x : CauchySequenceSpaceUp,
              cauchySequenceSpaceFromEventFlow (cauchySequenceSpaceToEventFlow x) = some x) ∧
              (∀ x y : CauchySequenceSpaceUp,
                cauchySequenceSpaceToEventFlow x = cauchySequenceSpaceToEventFlow y -> x = y) ∧
                cauchySequenceSpaceEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨cauchySequenceSpaceChapterTasteGate⟩
  · constructor
    · exact ⟨cauchySequenceSpaceFieldFaithful⟩
    · constructor
      · exact ⟨cauchySequenceSpaceNontrivial⟩
      · constructor
        · exact CauchySequenceSpaceTasteGate_single_carrier_alignment_decode_encode
        · constructor
          · exact CauchySequenceSpaceTasteGate_single_carrier_alignment_round_trip
          · constructor
            · intro x y heq
              exact CauchySequenceSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq
            · rfl

end BEDC.Derived.CauchySequenceSpaceUp.TasteGate
