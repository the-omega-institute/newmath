import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BudgetedRealSealRouteUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BudgetedRealSealRouteUp : Type where
  | mk :
      (selector threshold observationBudget limitSeal realSeal transport replay provenance
        localName : BHist) →
      BudgetedRealSealRouteUp
  deriving DecidableEq

def budgetedRealSealRouteEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: budgetedRealSealRouteEncodeBHist h
  | BHist.e1 h => BMark.b1 :: budgetedRealSealRouteEncodeBHist h

def budgetedRealSealRouteDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (budgetedRealSealRouteDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (budgetedRealSealRouteDecodeBHist tail)

private theorem BudgetedRealSealRouteTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, budgetedRealSealRouteDecodeBHist (budgetedRealSealRouteEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def budgetedRealSealRouteToEventFlow : BudgetedRealSealRouteUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BudgetedRealSealRouteUp.mk selector threshold observationBudget limitSeal realSeal transport
      replay provenance localName =>
      [[BMark.b0],
        budgetedRealSealRouteEncodeBHist selector,
        [BMark.b1, BMark.b0],
        budgetedRealSealRouteEncodeBHist threshold,
        [BMark.b1, BMark.b1, BMark.b0],
        budgetedRealSealRouteEncodeBHist observationBudget,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        budgetedRealSealRouteEncodeBHist limitSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        budgetedRealSealRouteEncodeBHist realSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        budgetedRealSealRouteEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        budgetedRealSealRouteEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        budgetedRealSealRouteEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        budgetedRealSealRouteEncodeBHist localName]

def budgetedRealSealRouteFromEventFlow : EventFlow → Option BudgetedRealSealRouteUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | selector :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | threshold :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | observationBudget :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | limitSeal :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | realSeal :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | transport :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | replay :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | provenance :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | localName :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (BudgetedRealSealRouteUp.mk
                                                                                  (budgetedRealSealRouteDecodeBHist
                                                                                    selector)
                                                                                  (budgetedRealSealRouteDecodeBHist
                                                                                    threshold)
                                                                                  (budgetedRealSealRouteDecodeBHist
                                                                                    observationBudget)
                                                                                  (budgetedRealSealRouteDecodeBHist
                                                                                    limitSeal)
                                                                                  (budgetedRealSealRouteDecodeBHist
                                                                                    realSeal)
                                                                                  (budgetedRealSealRouteDecodeBHist
                                                                                    transport)
                                                                                  (budgetedRealSealRouteDecodeBHist
                                                                                    replay)
                                                                                  (budgetedRealSealRouteDecodeBHist
                                                                                    provenance)
                                                                                  (budgetedRealSealRouteDecodeBHist
                                                                                    localName))
                                                                          | _ :: _ => none

private theorem BudgetedRealSealRouteTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BudgetedRealSealRouteUp,
      budgetedRealSealRouteFromEventFlow (budgetedRealSealRouteToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk selector threshold observationBudget limitSeal realSeal transport replay provenance
      localName =>
      change
        some
          (BudgetedRealSealRouteUp.mk
            (budgetedRealSealRouteDecodeBHist (budgetedRealSealRouteEncodeBHist selector))
            (budgetedRealSealRouteDecodeBHist (budgetedRealSealRouteEncodeBHist threshold))
            (budgetedRealSealRouteDecodeBHist
              (budgetedRealSealRouteEncodeBHist observationBudget))
            (budgetedRealSealRouteDecodeBHist (budgetedRealSealRouteEncodeBHist limitSeal))
            (budgetedRealSealRouteDecodeBHist (budgetedRealSealRouteEncodeBHist realSeal))
            (budgetedRealSealRouteDecodeBHist (budgetedRealSealRouteEncodeBHist transport))
            (budgetedRealSealRouteDecodeBHist (budgetedRealSealRouteEncodeBHist replay))
            (budgetedRealSealRouteDecodeBHist (budgetedRealSealRouteEncodeBHist provenance))
            (budgetedRealSealRouteDecodeBHist (budgetedRealSealRouteEncodeBHist localName))) =
          some
            (BudgetedRealSealRouteUp.mk selector threshold observationBudget limitSeal realSeal
              transport replay provenance localName)
      rw [BudgetedRealSealRouteTasteGate_single_carrier_alignment_decode_encode selector,
        BudgetedRealSealRouteTasteGate_single_carrier_alignment_decode_encode threshold,
        BudgetedRealSealRouteTasteGate_single_carrier_alignment_decode_encode observationBudget,
        BudgetedRealSealRouteTasteGate_single_carrier_alignment_decode_encode limitSeal,
        BudgetedRealSealRouteTasteGate_single_carrier_alignment_decode_encode realSeal,
        BudgetedRealSealRouteTasteGate_single_carrier_alignment_decode_encode transport,
        BudgetedRealSealRouteTasteGate_single_carrier_alignment_decode_encode replay,
        BudgetedRealSealRouteTasteGate_single_carrier_alignment_decode_encode provenance,
        BudgetedRealSealRouteTasteGate_single_carrier_alignment_decode_encode localName]

private theorem BudgetedRealSealRouteTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BudgetedRealSealRouteUp} :
    budgetedRealSealRouteToEventFlow x = budgetedRealSealRouteToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      budgetedRealSealRouteFromEventFlow (budgetedRealSealRouteToEventFlow x) =
        budgetedRealSealRouteFromEventFlow (budgetedRealSealRouteToEventFlow y) :=
    congrArg budgetedRealSealRouteFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BudgetedRealSealRouteTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (BudgetedRealSealRouteTasteGate_single_carrier_alignment_round_trip y)))

def budgetedRealSealRouteFields : BudgetedRealSealRouteUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BudgetedRealSealRouteUp.mk selector threshold observationBudget limitSeal realSeal transport
      replay provenance localName =>
      [selector, threshold, observationBudget, limitSeal, realSeal, transport, replay,
        provenance, localName]

private theorem BudgetedRealSealRouteTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : BudgetedRealSealRouteUp,
      budgetedRealSealRouteFields x = budgetedRealSealRouteFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk selector threshold observationBudget limitSeal realSeal transport replay provenance
      localName =>
      cases y with
      | mk selector' threshold' observationBudget' limitSeal' realSeal' transport' replay'
          provenance' localName' =>
          cases hfields
          rfl

instance budgetedRealSealRouteBHistCarrier : BHistCarrier BudgetedRealSealRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := budgetedRealSealRouteToEventFlow
  fromEventFlow := budgetedRealSealRouteFromEventFlow

instance budgetedRealSealRouteChapterTasteGate :
    ChapterTasteGate BudgetedRealSealRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      budgetedRealSealRouteFromEventFlow (budgetedRealSealRouteToEventFlow x) = some x
    exact BudgetedRealSealRouteTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BudgetedRealSealRouteTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance budgetedRealSealRouteFieldFaithful : FieldFaithful BudgetedRealSealRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := budgetedRealSealRouteFields
  field_faithful := BudgetedRealSealRouteTasteGate_single_carrier_alignment_field_faithful

instance budgetedRealSealRouteNontrivial : Nontrivial BudgetedRealSealRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BudgetedRealSealRouteUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BudgetedRealSealRouteUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BudgetedRealSealRouteUp :=
  -- BEDC touchpoint anchor: BHist BMark
  budgetedRealSealRouteChapterTasteGate

theorem BudgetedRealSealRouteTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      budgetedRealSealRouteDecodeBHist (budgetedRealSealRouteEncodeBHist h) = h) ∧
      (∀ x : BudgetedRealSealRouteUp,
        budgetedRealSealRouteFromEventFlow (budgetedRealSealRouteToEventFlow x) = some x) ∧
        (∀ x y : BudgetedRealSealRouteUp,
          budgetedRealSealRouteToEventFlow x = budgetedRealSealRouteToEventFlow y → x = y) ∧
          budgetedRealSealRouteEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact BudgetedRealSealRouteTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact BudgetedRealSealRouteTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact BudgetedRealSealRouteTasteGate_single_carrier_alignment_toEventFlow_injective heq
      · rfl

end BEDC.Derived.BudgetedRealSealRouteUp
