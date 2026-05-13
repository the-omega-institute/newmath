import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchySealBudgetSynchronizerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchySealBudgetSynchronizerUp : Type where
  | mk :
      (request sealRow budget tail selector compatibility transport route provenance nameCert :
        BHist) →
      CauchySealBudgetSynchronizerUp
  deriving DecidableEq

def cauchySealBudgetSynchronizerEncodeBHist : BHist → RawEvent
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchySealBudgetSynchronizerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchySealBudgetSynchronizerEncodeBHist h

def cauchySealBudgetSynchronizerDecodeBHist : RawEvent → BHist
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchySealBudgetSynchronizerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchySealBudgetSynchronizerDecodeBHist tail)

private theorem cauchySealBudgetSynchronizerDecode_encode_bhist :
    ∀ h : BHist,
      cauchySealBudgetSynchronizerDecodeBHist
        (cauchySealBudgetSynchronizerEncodeBHist h) = h := by
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cauchySealBudgetSynchronizerToEventFlow :
    CauchySealBudgetSynchronizerUp → EventFlow
  | CauchySealBudgetSynchronizerUp.mk request sealRow budget tail selector compatibility
      transport route provenance nameCert =>
      [[BMark.b0],
        cauchySealBudgetSynchronizerEncodeBHist request,
        [BMark.b1, BMark.b0],
        cauchySealBudgetSynchronizerEncodeBHist sealRow,
        [BMark.b1, BMark.b1, BMark.b0],
        cauchySealBudgetSynchronizerEncodeBHist budget,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchySealBudgetSynchronizerEncodeBHist tail,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchySealBudgetSynchronizerEncodeBHist selector,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchySealBudgetSynchronizerEncodeBHist compatibility,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchySealBudgetSynchronizerEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        cauchySealBudgetSynchronizerEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        cauchySealBudgetSynchronizerEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        cauchySealBudgetSynchronizerEncodeBHist nameCert]

def cauchySealBudgetSynchronizerFromEventFlow :
    EventFlow → Option CauchySealBudgetSynchronizerUp
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | request :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | sealRow :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | budget :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | tail :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | selector :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | compatibility :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | transport :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | route :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | provenance :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | nameCert :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      some
                                                                                        (CauchySealBudgetSynchronizerUp.mk
                                                                                          (cauchySealBudgetSynchronizerDecodeBHist
                                                                                            request)
                                                                                          (cauchySealBudgetSynchronizerDecodeBHist
                                                                                            sealRow)
                                                                                          (cauchySealBudgetSynchronizerDecodeBHist
                                                                                            budget)
                                                                                          (cauchySealBudgetSynchronizerDecodeBHist
                                                                                            tail)
                                                                                          (cauchySealBudgetSynchronizerDecodeBHist
                                                                                            selector)
                                                                                          (cauchySealBudgetSynchronizerDecodeBHist
                                                                                            compatibility)
                                                                                          (cauchySealBudgetSynchronizerDecodeBHist
                                                                                            transport)
                                                                                          (cauchySealBudgetSynchronizerDecodeBHist
                                                                                            route)
                                                                                          (cauchySealBudgetSynchronizerDecodeBHist
                                                                                            provenance)
                                                                                          (cauchySealBudgetSynchronizerDecodeBHist
                                                                                            nameCert))
                                                                                  | _ :: _ => none

private theorem cauchySealBudgetSynchronizer_round_trip :
    ∀ x : CauchySealBudgetSynchronizerUp,
      cauchySealBudgetSynchronizerFromEventFlow
        (cauchySealBudgetSynchronizerToEventFlow x) = some x := by
  intro x
  cases x with
  | mk request sealRow budget tail selector compatibility transport route provenance nameCert =>
      change
        some
          (CauchySealBudgetSynchronizerUp.mk
            (cauchySealBudgetSynchronizerDecodeBHist
              (cauchySealBudgetSynchronizerEncodeBHist request))
            (cauchySealBudgetSynchronizerDecodeBHist
              (cauchySealBudgetSynchronizerEncodeBHist sealRow))
            (cauchySealBudgetSynchronizerDecodeBHist
              (cauchySealBudgetSynchronizerEncodeBHist budget))
            (cauchySealBudgetSynchronizerDecodeBHist
              (cauchySealBudgetSynchronizerEncodeBHist tail))
            (cauchySealBudgetSynchronizerDecodeBHist
              (cauchySealBudgetSynchronizerEncodeBHist selector))
            (cauchySealBudgetSynchronizerDecodeBHist
              (cauchySealBudgetSynchronizerEncodeBHist compatibility))
            (cauchySealBudgetSynchronizerDecodeBHist
              (cauchySealBudgetSynchronizerEncodeBHist transport))
            (cauchySealBudgetSynchronizerDecodeBHist
              (cauchySealBudgetSynchronizerEncodeBHist route))
            (cauchySealBudgetSynchronizerDecodeBHist
              (cauchySealBudgetSynchronizerEncodeBHist provenance))
            (cauchySealBudgetSynchronizerDecodeBHist
              (cauchySealBudgetSynchronizerEncodeBHist nameCert))) =
          some
            (CauchySealBudgetSynchronizerUp.mk request sealRow budget tail selector
              compatibility transport route provenance nameCert)
      rw [cauchySealBudgetSynchronizerDecode_encode_bhist request,
        cauchySealBudgetSynchronizerDecode_encode_bhist sealRow,
        cauchySealBudgetSynchronizerDecode_encode_bhist budget,
        cauchySealBudgetSynchronizerDecode_encode_bhist tail,
        cauchySealBudgetSynchronizerDecode_encode_bhist selector,
        cauchySealBudgetSynchronizerDecode_encode_bhist compatibility,
        cauchySealBudgetSynchronizerDecode_encode_bhist transport,
        cauchySealBudgetSynchronizerDecode_encode_bhist route,
        cauchySealBudgetSynchronizerDecode_encode_bhist provenance,
        cauchySealBudgetSynchronizerDecode_encode_bhist nameCert]

private theorem cauchySealBudgetSynchronizerToEventFlow_injective
    {x y : CauchySealBudgetSynchronizerUp} :
    cauchySealBudgetSynchronizerToEventFlow x =
      cauchySealBudgetSynchronizerToEventFlow y → x = y := by
  intro heq
  have hread :
      cauchySealBudgetSynchronizerFromEventFlow
          (cauchySealBudgetSynchronizerToEventFlow x) =
        cauchySealBudgetSynchronizerFromEventFlow
          (cauchySealBudgetSynchronizerToEventFlow y) :=
    congrArg cauchySealBudgetSynchronizerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchySealBudgetSynchronizer_round_trip x).symm
      (Eq.trans hread (cauchySealBudgetSynchronizer_round_trip y)))

instance cauchySealBudgetSynchronizerBHistCarrier :
    BHistCarrier CauchySealBudgetSynchronizerUp where
  toEventFlow := cauchySealBudgetSynchronizerToEventFlow
  fromEventFlow := cauchySealBudgetSynchronizerFromEventFlow

instance cauchySealBudgetSynchronizerChapterTasteGate :
    ChapterTasteGate CauchySealBudgetSynchronizerUp where
  round_trip := by
    intro x
    change
      cauchySealBudgetSynchronizerFromEventFlow
          (cauchySealBudgetSynchronizerToEventFlow x) =
        some x
    exact cauchySealBudgetSynchronizer_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchySealBudgetSynchronizerToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchySealBudgetSynchronizerUp :=
  cauchySealBudgetSynchronizerChapterTasteGate

instance cauchySealBudgetSynchronizerNontrivial :
    Nontrivial CauchySealBudgetSynchronizerUp where
  witness_pair :=
    ⟨CauchySealBudgetSynchronizerUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      CauchySealBudgetSynchronizerUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

instance cauchySealBudgetSynchronizerFieldFaithful :
    FieldFaithful CauchySealBudgetSynchronizerUp where
  fields := fun x =>
    match x with
    | CauchySealBudgetSynchronizerUp.mk request sealRow budget tail selector compatibility
        transport route provenance nameCert =>
        [request, sealRow, budget, tail, selector, compatibility, transport, route, provenance,
          nameCert]
  field_faithful := by
    intro x y hfields
    cases x with
    | mk request sealRow budget tail selector compatibility transport route provenance nameCert =>
        cases y with
        | mk request' sealRow' budget' tail' selector' compatibility' transport' route'
            provenance' nameCert' =>
            injection hfields with hRequest hTail0
            injection hTail0 with hSealRow hTail1
            injection hTail1 with hBudget hTail2
            injection hTail2 with hTail hTail3
            injection hTail3 with hSelector hTail4
            injection hTail4 with hCompatibility hTail5
            injection hTail5 with hTransport hTail6
            injection hTail6 with hRoute hTail7
            injection hTail7 with hProvenance hTail8
            injection hTail8 with hNameCert _hNil
            cases hRequest
            cases hSealRow
            cases hBudget
            cases hTail
            cases hSelector
            cases hCompatibility
            cases hTransport
            cases hRoute
            cases hProvenance
            cases hNameCert
            rfl

instance cauchySealBudgetSynchronizerStructurallyAtomic :
    StructurallyAtomic CauchySealBudgetSynchronizerUp where
  nearest_siblings :=
    ["CauchyLimitSealUp", "CauchyDiagonalBudgetUp", "RealObservationBudgetUp",
      "TailCofinalityScheduleUp", "DiagonalTailSelectorUp"]
  not_reducible_witness :=
    "joint compatibility row ties selector, budget, shared threshold, and sealRow rows"

theorem CauchySealBudgetSynchronizerTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchySealBudgetSynchronizerDecodeBHist
        (cauchySealBudgetSynchronizerEncodeBHist h) = h) ∧
      (∀ x : CauchySealBudgetSynchronizerUp,
        cauchySealBudgetSynchronizerFromEventFlow
          (cauchySealBudgetSynchronizerToEventFlow x) = some x) ∧
        (∀ x y : CauchySealBudgetSynchronizerUp,
          cauchySealBudgetSynchronizerToEventFlow x =
            cauchySealBudgetSynchronizerToEventFlow y → x = y) ∧
          (∀ x y : CauchySealBudgetSynchronizerUp,
            FieldFaithful.fields x = FieldFaithful.fields y → x = y) ∧
            (∃ x y : CauchySealBudgetSynchronizerUp, x ≠ y) := by
  constructor
  · exact cauchySealBudgetSynchronizerDecode_encode_bhist
  · constructor
    · exact cauchySealBudgetSynchronizer_round_trip
    · constructor
      · intro x y heq
        exact cauchySealBudgetSynchronizerToEventFlow_injective heq
      · constructor
        · intro x y hfields
          cases x with
          | mk request sealRow budget tail selector compatibility transport route provenance nameCert =>
              cases y with
              | mk request' sealRow' budget' tail' selector' compatibility' transport' route'
                  provenance' nameCert' =>
                  injection hfields with hRequest hTail0
                  injection hTail0 with hSealRow hTail1
                  injection hTail1 with hBudget hTail2
                  injection hTail2 with hTail hTail3
                  injection hTail3 with hSelector hTail4
                  injection hTail4 with hCompatibility hTail5
                  injection hTail5 with hTransport hTail6
                  injection hTail6 with hRoute hTail7
                  injection hTail7 with hProvenance hTail8
                  injection hTail8 with hNameCert _hNil
                  cases hRequest
                  cases hSealRow
                  cases hBudget
                  cases hTail
                  cases hSelector
                  cases hCompatibility
                  cases hTransport
                  cases hRoute
                  cases hProvenance
                  cases hNameCert
                  rfl
        · refine
            ⟨CauchySealBudgetSynchronizerUp.mk BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty,
              CauchySealBudgetSynchronizerUp.mk (BHist.e0 BHist.Empty) BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty, ?_⟩
          intro h
          cases h

end BEDC.Derived.CauchySealBudgetSynchronizerUp
