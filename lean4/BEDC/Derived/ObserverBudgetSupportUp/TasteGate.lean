import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ObserverBudgetSupportUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ObserverBudgetSupportUp : Type where
  | mk :
      (observerFrame finiteSupport crossHistCausal budgetSelector supportTransport
        componentTransport displayedReplay provenance name : BHist) →
      ObserverBudgetSupportUp

def observerBudgetSupportEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: observerBudgetSupportEncodeBHist h
  | BHist.e1 h => BMark.b1 :: observerBudgetSupportEncodeBHist h

def observerBudgetSupportDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (observerBudgetSupportDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (observerBudgetSupportDecodeBHist tail)

private theorem observerBudgetSupportDecode_encode_bhist :
    ∀ h : BHist,
      observerBudgetSupportDecodeBHist (observerBudgetSupportEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem observerBudgetSupport_mk_congr
    {observerFrame observerFrame' finiteSupport finiteSupport' crossHistCausal
      crossHistCausal' budgetSelector budgetSelector' supportTransport supportTransport'
      componentTransport componentTransport' displayedReplay displayedReplay' provenance
      provenance' name name' : BHist}
    (hFrame : observerFrame' = observerFrame)
    (hSupport : finiteSupport' = finiteSupport)
    (hCausal : crossHistCausal' = crossHistCausal)
    (hBudget : budgetSelector' = budgetSelector)
    (hTransport : supportTransport' = supportTransport)
    (hComponent : componentTransport' = componentTransport)
    (hReplay : displayedReplay' = displayedReplay)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    ObserverBudgetSupportUp.mk observerFrame' finiteSupport' crossHistCausal' budgetSelector'
        supportTransport' componentTransport' displayedReplay' provenance' name' =
      ObserverBudgetSupportUp.mk observerFrame finiteSupport crossHistCausal budgetSelector
        supportTransport componentTransport displayedReplay provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hFrame
  cases hSupport
  cases hCausal
  cases hBudget
  cases hTransport
  cases hComponent
  cases hReplay
  cases hProvenance
  cases hName
  rfl

def observerBudgetSupportToEventFlow : ObserverBudgetSupportUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ObserverBudgetSupportUp.mk observerFrame finiteSupport crossHistCausal budgetSelector
      supportTransport componentTransport displayedReplay provenance name =>
      [[BMark.b0],
        observerBudgetSupportEncodeBHist observerFrame,
        [BMark.b1, BMark.b0],
        observerBudgetSupportEncodeBHist finiteSupport,
        [BMark.b1, BMark.b1, BMark.b0],
        observerBudgetSupportEncodeBHist crossHistCausal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerBudgetSupportEncodeBHist budgetSelector,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerBudgetSupportEncodeBHist supportTransport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerBudgetSupportEncodeBHist componentTransport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerBudgetSupportEncodeBHist displayedReplay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        observerBudgetSupportEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        observerBudgetSupportEncodeBHist name]

def observerBudgetSupportFromEventFlow : EventFlow → Option ObserverBudgetSupportUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | observerFrame :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | finiteSupport :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | crossHistCausal :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | budgetSelector :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | supportTransport :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | componentTransport :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | displayedReplay :: rest13 =>
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
                                                                      | name :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (ObserverBudgetSupportUp.mk
                                                                                  (observerBudgetSupportDecodeBHist
                                                                                    observerFrame)
                                                                                  (observerBudgetSupportDecodeBHist
                                                                                    finiteSupport)
                                                                                  (observerBudgetSupportDecodeBHist
                                                                                    crossHistCausal)
                                                                                  (observerBudgetSupportDecodeBHist
                                                                                    budgetSelector)
                                                                                  (observerBudgetSupportDecodeBHist
                                                                                    supportTransport)
                                                                                  (observerBudgetSupportDecodeBHist
                                                                                    componentTransport)
                                                                                  (observerBudgetSupportDecodeBHist
                                                                                    displayedReplay)
                                                                                  (observerBudgetSupportDecodeBHist
                                                                                    provenance)
                                                                                  (observerBudgetSupportDecodeBHist
                                                                                    name))
                                                                          | _ :: _ => none

private theorem observerBudgetSupport_round_trip :
    ∀ x : ObserverBudgetSupportUp,
      observerBudgetSupportFromEventFlow (observerBudgetSupportToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk observerFrame finiteSupport crossHistCausal budgetSelector supportTransport
      componentTransport displayedReplay provenance name =>
      change
        some
          (ObserverBudgetSupportUp.mk
            (observerBudgetSupportDecodeBHist
              (observerBudgetSupportEncodeBHist observerFrame))
            (observerBudgetSupportDecodeBHist
              (observerBudgetSupportEncodeBHist finiteSupport))
            (observerBudgetSupportDecodeBHist
              (observerBudgetSupportEncodeBHist crossHistCausal))
            (observerBudgetSupportDecodeBHist
              (observerBudgetSupportEncodeBHist budgetSelector))
            (observerBudgetSupportDecodeBHist
              (observerBudgetSupportEncodeBHist supportTransport))
            (observerBudgetSupportDecodeBHist
              (observerBudgetSupportEncodeBHist componentTransport))
            (observerBudgetSupportDecodeBHist
              (observerBudgetSupportEncodeBHist displayedReplay))
            (observerBudgetSupportDecodeBHist
              (observerBudgetSupportEncodeBHist provenance))
            (observerBudgetSupportDecodeBHist
              (observerBudgetSupportEncodeBHist name))) =
          some
            (ObserverBudgetSupportUp.mk observerFrame finiteSupport crossHistCausal
              budgetSelector supportTransport componentTransport displayedReplay provenance name)
      exact
        congrArg some
          (observerBudgetSupport_mk_congr
            (observerBudgetSupportDecode_encode_bhist observerFrame)
            (observerBudgetSupportDecode_encode_bhist finiteSupport)
            (observerBudgetSupportDecode_encode_bhist crossHistCausal)
            (observerBudgetSupportDecode_encode_bhist budgetSelector)
            (observerBudgetSupportDecode_encode_bhist supportTransport)
            (observerBudgetSupportDecode_encode_bhist componentTransport)
            (observerBudgetSupportDecode_encode_bhist displayedReplay)
            (observerBudgetSupportDecode_encode_bhist provenance)
            (observerBudgetSupportDecode_encode_bhist name))

private theorem observerBudgetSupportToEventFlow_injective {x y : ObserverBudgetSupportUp} :
    observerBudgetSupportToEventFlow x = observerBudgetSupportToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      observerBudgetSupportFromEventFlow (observerBudgetSupportToEventFlow x) =
        observerBudgetSupportFromEventFlow (observerBudgetSupportToEventFlow y) :=
    congrArg observerBudgetSupportFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (observerBudgetSupport_round_trip x).symm
      (Eq.trans hread (observerBudgetSupport_round_trip y)))

instance observerBudgetSupportBHistCarrier : BHistCarrier ObserverBudgetSupportUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := observerBudgetSupportToEventFlow
  fromEventFlow := observerBudgetSupportFromEventFlow

instance observerBudgetSupportChapterTasteGate :
    ChapterTasteGate ObserverBudgetSupportUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change observerBudgetSupportFromEventFlow (observerBudgetSupportToEventFlow x) = some x
    exact observerBudgetSupport_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (observerBudgetSupportToEventFlow_injective heq)

def taste_gate : ChapterTasteGate ObserverBudgetSupportUp :=
  -- BEDC touchpoint anchor: BHist BMark
  observerBudgetSupportChapterTasteGate

instance observerBudgetSupportFieldFaithful :
    FieldFaithful ObserverBudgetSupportUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | ObserverBudgetSupportUp.mk observerFrame finiteSupport crossHistCausal budgetSelector
        supportTransport componentTransport displayedReplay provenance name =>
        [observerFrame, finiteSupport, crossHistCausal, budgetSelector, supportTransport,
          componentTransport, displayedReplay, provenance, name]
  field_faithful := by
    intro x y h
    cases x with
    | mk observerFrame₁ finiteSupport₁ crossHistCausal₁ budgetSelector₁ supportTransport₁
        componentTransport₁ displayedReplay₁ provenance₁ name₁ =>
        cases y with
        | mk observerFrame₂ finiteSupport₂ crossHistCausal₂ budgetSelector₂ supportTransport₂
            componentTransport₂ displayedReplay₂ provenance₂ name₂ =>
            simp only [] at h
            injection h with hFrame hRest₁
            injection hRest₁ with hSupport hRest₂
            injection hRest₂ with hCausal hRest₃
            injection hRest₃ with hBudget hRest₄
            injection hRest₄ with hTransport hRest₅
            injection hRest₅ with hComponent hRest₆
            injection hRest₆ with hReplay hRest₇
            injection hRest₇ with hProvenance hRest₈
            injection hRest₈ with hName _
            subst hFrame
            subst hSupport
            subst hCausal
            subst hBudget
            subst hTransport
            subst hComponent
            subst hReplay
            subst hProvenance
            subst hName
            rfl

instance observerBudgetSupportNontrivial : Nontrivial ObserverBudgetSupportUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ObserverBudgetSupportUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ObserverBudgetSupportUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem ObserverBudgetSupportTasteGate_carrier_recognition :
    (∀ x : ObserverBudgetSupportUp,
        observerBudgetSupportFromEventFlow (observerBudgetSupportToEventFlow x) = some x) ∧
      (observerBudgetSupportFromEventFlow
          (observerBudgetSupportToEventFlow
            (ObserverBudgetSupportUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty)) =
        some
          (ObserverBudgetSupportUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty)) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro x
    exact observerBudgetSupport_round_trip x
  · exact
      observerBudgetSupport_round_trip
        (ObserverBudgetSupportUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty)

end BEDC.Derived.ObserverBudgetSupportUp
