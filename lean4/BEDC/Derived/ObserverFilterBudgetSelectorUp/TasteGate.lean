import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ObserverFilterBudgetSelectorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ObserverFilterBudgetSelectorUp : Type where
  | mk
      (filter identity selected omitted budget window dyadic handoff realSeal transport route
        provenance name : BHist) :
      ObserverFilterBudgetSelectorUp
  deriving DecidableEq

def observerFilterBudgetSelectorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: observerFilterBudgetSelectorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: observerFilterBudgetSelectorEncodeBHist h

def observerFilterBudgetSelectorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (observerFilterBudgetSelectorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (observerFilterBudgetSelectorDecodeBHist tail)

private theorem observerFilterBudgetSelectorDecode_encode_bhist :
    ∀ h : BHist,
      observerFilterBudgetSelectorDecodeBHist
        (observerFilterBudgetSelectorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def observerFilterBudgetSelectorDecodePacket
    (filter identity selected omitted budget window dyadic handoff realSeal transport route
      provenance name : RawEvent) :
    ObserverFilterBudgetSelectorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  ObserverFilterBudgetSelectorUp.mk
    (observerFilterBudgetSelectorDecodeBHist filter)
    (observerFilterBudgetSelectorDecodeBHist identity)
    (observerFilterBudgetSelectorDecodeBHist selected)
    (observerFilterBudgetSelectorDecodeBHist omitted)
    (observerFilterBudgetSelectorDecodeBHist budget)
    (observerFilterBudgetSelectorDecodeBHist window)
    (observerFilterBudgetSelectorDecodeBHist dyadic)
    (observerFilterBudgetSelectorDecodeBHist handoff)
    (observerFilterBudgetSelectorDecodeBHist realSeal)
    (observerFilterBudgetSelectorDecodeBHist transport)
    (observerFilterBudgetSelectorDecodeBHist route)
    (observerFilterBudgetSelectorDecodeBHist provenance)
    (observerFilterBudgetSelectorDecodeBHist name)

def observerFilterBudgetSelectorToEventFlow :
    ObserverFilterBudgetSelectorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ObserverFilterBudgetSelectorUp.mk filter identity selected omitted budget window dyadic
      handoff realSeal transport route provenance name =>
      [observerFilterBudgetSelectorEncodeBHist filter,
        observerFilterBudgetSelectorEncodeBHist identity,
        observerFilterBudgetSelectorEncodeBHist selected,
        observerFilterBudgetSelectorEncodeBHist omitted,
        observerFilterBudgetSelectorEncodeBHist budget,
        observerFilterBudgetSelectorEncodeBHist window,
        observerFilterBudgetSelectorEncodeBHist dyadic,
        observerFilterBudgetSelectorEncodeBHist handoff,
        observerFilterBudgetSelectorEncodeBHist realSeal,
        observerFilterBudgetSelectorEncodeBHist transport,
        observerFilterBudgetSelectorEncodeBHist route,
        observerFilterBudgetSelectorEncodeBHist provenance,
        observerFilterBudgetSelectorEncodeBHist name]

def observerFilterBudgetSelectorFromEventFlow :
    EventFlow → Option ObserverFilterBudgetSelectorUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | filter :: rest0 =>
      match rest0 with
      | [] => none
      | identity :: rest1 =>
          match rest1 with
          | [] => none
          | selected :: rest2 =>
              match rest2 with
              | [] => none
              | omitted :: rest3 =>
                  match rest3 with
                  | [] => none
                  | budget :: rest4 =>
                      match rest4 with
                      | [] => none
                      | window :: rest5 =>
                          match rest5 with
                          | [] => none
                          | dyadic :: rest6 =>
                              match rest6 with
                              | [] => none
                              | handoff :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | realSeal :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | transport :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | route :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | provenance :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | name :: rest12 =>
                                                      match rest12 with
                                                      | [] =>
                                                          some
                                                            (observerFilterBudgetSelectorDecodePacket
                                                              filter identity selected omitted budget
                                                              window dyadic handoff realSeal
                                                              transport route provenance name)
                                                      | _ :: _ => none

private theorem observerFilterBudgetSelector_round_trip :
    ∀ x : ObserverFilterBudgetSelectorUp,
      observerFilterBudgetSelectorFromEventFlow
        (observerFilterBudgetSelectorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk filter identity selected omitted budget window dyadic handoff realSeal transport route
      provenance name =>
      change
        some
            (observerFilterBudgetSelectorDecodePacket
              (observerFilterBudgetSelectorEncodeBHist filter)
              (observerFilterBudgetSelectorEncodeBHist identity)
              (observerFilterBudgetSelectorEncodeBHist selected)
              (observerFilterBudgetSelectorEncodeBHist omitted)
              (observerFilterBudgetSelectorEncodeBHist budget)
              (observerFilterBudgetSelectorEncodeBHist window)
              (observerFilterBudgetSelectorEncodeBHist dyadic)
              (observerFilterBudgetSelectorEncodeBHist handoff)
              (observerFilterBudgetSelectorEncodeBHist realSeal)
              (observerFilterBudgetSelectorEncodeBHist transport)
              (observerFilterBudgetSelectorEncodeBHist route)
              (observerFilterBudgetSelectorEncodeBHist provenance)
              (observerFilterBudgetSelectorEncodeBHist name)) =
          some
            (ObserverFilterBudgetSelectorUp.mk filter identity selected omitted budget window
              dyadic handoff realSeal transport route provenance name)
      unfold observerFilterBudgetSelectorDecodePacket
      rw [observerFilterBudgetSelectorDecode_encode_bhist filter,
        observerFilterBudgetSelectorDecode_encode_bhist identity,
        observerFilterBudgetSelectorDecode_encode_bhist selected,
        observerFilterBudgetSelectorDecode_encode_bhist omitted,
        observerFilterBudgetSelectorDecode_encode_bhist budget,
        observerFilterBudgetSelectorDecode_encode_bhist window,
        observerFilterBudgetSelectorDecode_encode_bhist dyadic,
        observerFilterBudgetSelectorDecode_encode_bhist handoff,
        observerFilterBudgetSelectorDecode_encode_bhist realSeal,
        observerFilterBudgetSelectorDecode_encode_bhist transport,
        observerFilterBudgetSelectorDecode_encode_bhist route,
        observerFilterBudgetSelectorDecode_encode_bhist provenance,
        observerFilterBudgetSelectorDecode_encode_bhist name]

private theorem observerFilterBudgetSelectorToEventFlow_injective
    {x y : ObserverFilterBudgetSelectorUp} :
    observerFilterBudgetSelectorToEventFlow x =
      observerFilterBudgetSelectorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      observerFilterBudgetSelectorFromEventFlow
          (observerFilterBudgetSelectorToEventFlow x) =
        observerFilterBudgetSelectorFromEventFlow
          (observerFilterBudgetSelectorToEventFlow y) :=
    congrArg observerFilterBudgetSelectorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (observerFilterBudgetSelector_round_trip x).symm
      (Eq.trans hread (observerFilterBudgetSelector_round_trip y)))

def observerFilterBudgetSelectorFields :
    ObserverFilterBudgetSelectorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ObserverFilterBudgetSelectorUp.mk filter identity selected omitted budget window dyadic
      handoff realSeal transport route provenance name =>
      [filter, identity, selected, omitted, budget, window, dyadic, handoff, realSeal,
        transport, route, provenance, name]

private theorem observerFilterBudgetSelector_fields_faithful :
    ∀ x y : ObserverFilterBudgetSelectorUp,
      observerFilterBudgetSelectorFields x =
        observerFilterBudgetSelectorFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  exact observerFilterBudgetSelectorToEventFlow_injective (by
    cases x with
    | mk filter₁ identity₁ selected₁ omitted₁ budget₁ window₁ dyadic₁ handoff₁ realSeal₁
        transport₁ route₁ provenance₁ name₁ =>
        cases y with
        | mk filter₂ identity₂ selected₂ omitted₂ budget₂ window₂ dyadic₂ handoff₂ realSeal₂
            transport₂ route₂ provenance₂ name₂ =>
            injection hfields with hFilter tail0
            injection tail0 with hIdentity tail1
            injection tail1 with hSelected tail2
            injection tail2 with hOmitted tail3
            injection tail3 with hBudget tail4
            injection tail4 with hWindow tail5
            injection tail5 with hDyadic tail6
            injection tail6 with hHandoff tail7
            injection tail7 with hSeal tail8
            injection tail8 with hTransport tail9
            injection tail9 with hRoute tail10
            injection tail10 with hProvenance tail11
            injection tail11 with hName _
            subst hFilter
            subst hIdentity
            subst hSelected
            subst hOmitted
            subst hBudget
            subst hWindow
            subst hDyadic
            subst hHandoff
            subst hSeal
            subst hTransport
            subst hRoute
            subst hProvenance
            subst hName
            rfl)

instance observerFilterBudgetSelectorBHistCarrier :
    BHistCarrier ObserverFilterBudgetSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := observerFilterBudgetSelectorToEventFlow
  fromEventFlow := observerFilterBudgetSelectorFromEventFlow

instance observerFilterBudgetSelectorChapterTasteGate :
    ChapterTasteGate ObserverFilterBudgetSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      observerFilterBudgetSelectorFromEventFlow
        (observerFilterBudgetSelectorToEventFlow x) = some x
    exact observerFilterBudgetSelector_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (observerFilterBudgetSelectorToEventFlow_injective heq)

def taste_gate : ChapterTasteGate ObserverFilterBudgetSelectorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  observerFilterBudgetSelectorChapterTasteGate

instance observerFilterBudgetSelectorFieldFaithful :
    FieldFaithful ObserverFilterBudgetSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := observerFilterBudgetSelectorFields
  field_faithful := observerFilterBudgetSelector_fields_faithful

instance observerFilterBudgetSelectorNontrivial :
    Nontrivial ObserverFilterBudgetSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ObserverFilterBudgetSelectorUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      ObserverFilterBudgetSelectorUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem ObserverFilterBudgetSelectorTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      observerFilterBudgetSelectorDecodeBHist
        (observerFilterBudgetSelectorEncodeBHist h) = h) ∧
      (∀ x : ObserverFilterBudgetSelectorUp,
        observerFilterBudgetSelectorFromEventFlow
          (observerFilterBudgetSelectorToEventFlow x) = some x) ∧
        (∀ x y : ObserverFilterBudgetSelectorUp,
          observerFilterBudgetSelectorToEventFlow x =
            observerFilterBudgetSelectorToEventFlow y → x = y) ∧
          observerFilterBudgetSelectorEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact observerFilterBudgetSelectorDecode_encode_bhist
  · constructor
    · intro x
      change
        observerFilterBudgetSelectorFromEventFlow
          (observerFilterBudgetSelectorToEventFlow x) = some x
      exact observerFilterBudgetSelector_round_trip x
    · constructor
      · intro x y heq
        exact observerFilterBudgetSelectorToEventFlow_injective heq
      · rfl

theorem ObserverFilterBudgetSelectorNameCertSurface_omitted_field_empty_reflects
    (filter identity selected omitted budget window dyadic handoff realSeal transport route
      provenance name : BHist)
    (hfields :
      observerFilterBudgetSelectorFields
          (ObserverFilterBudgetSelectorUp.mk filter identity selected omitted budget window
            dyadic handoff realSeal transport route provenance name) =
        observerFilterBudgetSelectorFields
          (ObserverFilterBudgetSelectorUp.mk filter identity selected BHist.Empty budget
            window dyadic handoff realSeal transport route provenance name)) :
    omitted = BHist.Empty := by
  -- BEDC touchpoint anchor: BHist BMark
  injection hfields with _ tail0
  injection tail0 with _ tail1
  injection tail1 with _ tail2
  injection tail2 with hOmitted _

theorem ObserverFilterBudgetSelectorStreamNameHandoff_omitted_boundary_not_erased
    (filter identity selected budget window dyadic handoff realSeal transport route
      provenance name : BHist) :
    observerFilterBudgetSelectorToEventFlow
        (ObserverFilterBudgetSelectorUp.mk filter identity selected (BHist.e0 BHist.Empty)
          budget window dyadic handoff realSeal transport route provenance name) ≠
      observerFilterBudgetSelectorToEventFlow
        (ObserverFilterBudgetSelectorUp.mk filter identity selected BHist.Empty budget
          window dyadic handoff realSeal transport route provenance name) := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  injection heq with _ tail0
  injection tail0 with _ tail1
  injection tail1 with _ tail2
  injection tail2 with homitted _
  cases homitted

theorem ObserverFilterBudgetSelectorOmittedRowExclusion_omitted_boundary_not_repacked
    (filter identity selected budget window dyadic handoff realSeal transport route provenance
      name : BHist) :
    observerFilterBudgetSelectorToEventFlow
        (ObserverFilterBudgetSelectorUp.mk filter identity selected BHist.Empty budget window
          dyadic handoff realSeal transport route provenance name) ≠
      observerFilterBudgetSelectorToEventFlow
        (ObserverFilterBudgetSelectorUp.mk filter identity selected (BHist.e0 BHist.Empty)
          budget window dyadic handoff realSeal transport route provenance name) := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  injection heq with _ tail0
  injection tail0 with _ tail1
  injection tail1 with _ tail2
  injection tail2 with homitted _
  cases homitted

theorem ObserverFilterBudgetSelectorRealSealTerminality_terminal_field_not_erased
    (filter identity selected omitted budget window dyadic handoff transport route provenance
      name : BHist) :
    observerFilterBudgetSelectorToEventFlow
        (ObserverFilterBudgetSelectorUp.mk filter identity selected omitted budget window
          dyadic handoff (BHist.e0 BHist.Empty) transport route provenance name) ≠
      observerFilterBudgetSelectorToEventFlow
        (ObserverFilterBudgetSelectorUp.mk filter identity selected omitted budget window
          dyadic handoff BHist.Empty transport route provenance name) := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  injection heq with _ tail0
  injection tail0 with _ tail1
  injection tail1 with _ tail2
  injection tail2 with _ tail3
  injection tail3 with _ tail4
  injection tail4 with _ tail5
  injection tail5 with _ tail6
  injection tail6 with _ tail7
  injection tail7 with hSeal _
  cases hSeal

theorem ObserverFilterBudgetSelectorDyadicReadbackExactness_dyadic_field_not_erased
    (filter identity selected omitted budget window handoff realSeal transport route provenance
      name : BHist) :
    observerFilterBudgetSelectorToEventFlow
        (ObserverFilterBudgetSelectorUp.mk filter identity selected omitted budget window
          (BHist.e0 BHist.Empty) handoff realSeal transport route provenance name) ≠
      observerFilterBudgetSelectorToEventFlow
        (ObserverFilterBudgetSelectorUp.mk filter identity selected omitted budget window
          BHist.Empty handoff realSeal transport route provenance name) := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  injection heq with _ tail0
  injection tail0 with _ tail1
  injection tail1 with _ tail2
  injection tail2 with _ tail3
  injection tail3 with _ tail4
  injection tail4 with _ tail5
  injection tail5 with hDyadic _
  cases hDyadic

theorem ObserverFilterBudgetSelectorSelectedRowGate_selected_field_not_erased
    (filter identity omitted budget window dyadic handoff realSeal transport route provenance
      name : BHist) :
    observerFilterBudgetSelectorToEventFlow
        (ObserverFilterBudgetSelectorUp.mk filter identity (BHist.e0 BHist.Empty) omitted
          budget window dyadic handoff realSeal transport route provenance name) ≠
      observerFilterBudgetSelectorToEventFlow
        (ObserverFilterBudgetSelectorUp.mk filter identity BHist.Empty omitted budget window
          dyadic handoff realSeal transport route provenance name) := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  injection heq with _ tail0
  injection tail0 with _ tail1
  injection tail1 with hSelected _
  cases hSelected

theorem ObserverFilterBudgetSelectorBudgetRefinementNonescape_budget_field_not_erased
    (filter identity selected omitted window dyadic handoff realSeal transport route provenance
      name : BHist) :
    observerFilterBudgetSelectorToEventFlow
        (ObserverFilterBudgetSelectorUp.mk filter identity selected omitted
          (BHist.e0 BHist.Empty) window dyadic handoff realSeal transport route provenance
          name) ≠
      observerFilterBudgetSelectorToEventFlow
        (ObserverFilterBudgetSelectorUp.mk filter identity selected omitted BHist.Empty window
          dyadic handoff realSeal transport route provenance name) := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  injection heq with _ tail0
  injection tail0 with _ tail1
  injection tail1 with _ tail2
  injection tail2 with _ tail3
  injection tail3 with hBudget _
  cases hBudget

theorem ObserverFilterBudgetSelectorBridgeReadyRoute_support_fields_faithful
    (filter identity selected omitted budget window dyadic handoff realSeal transport route
      provenance name : BHist)
    (hfields :
      observerFilterBudgetSelectorFields
          (ObserverFilterBudgetSelectorUp.mk filter identity selected omitted budget window
            dyadic handoff realSeal transport route provenance name) =
        observerFilterBudgetSelectorFields
          (ObserverFilterBudgetSelectorUp.mk filter identity selected omitted budget window
            dyadic handoff realSeal BHist.Empty BHist.Empty BHist.Empty BHist.Empty)) :
    transport = BHist.Empty ∧ route = BHist.Empty ∧ provenance = BHist.Empty ∧
      name = BHist.Empty := by
  -- BEDC touchpoint anchor: BHist BMark
  injection hfields with _ tail0
  injection tail0 with _ tail1
  injection tail1 with _ tail2
  injection tail2 with _ tail3
  injection tail3 with _ tail4
  injection tail4 with _ tail5
  injection tail5 with _ tail6
  injection tail6 with _ tail7
  injection tail7 with _ tail8
  injection tail8 with hTransport tail9
  injection tail9 with hRoute tail10
  injection tail10 with hProvenance tail11
  injection tail11 with hName _
  exact ⟨hTransport, hRoute, hProvenance, hName⟩

end BEDC.Derived.ObserverFilterBudgetSelectorUp
