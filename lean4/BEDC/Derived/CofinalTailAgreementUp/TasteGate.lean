import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CofinalTailAgreementUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CofinalTailAgreementUp : Type where
  | mk :
      (meet fusion budget sealRow dyadicRow readback handoff transport routes provenance
        name : BHist) →
      CofinalTailAgreementUp
  deriving DecidableEq

def cofinalTailAgreementEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cofinalTailAgreementEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cofinalTailAgreementEncodeBHist h

def cofinalTailAgreementDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cofinalTailAgreementDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cofinalTailAgreementDecodeBHist tail)

private theorem CofinalTailAgreementTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cofinalTailAgreementDecodeBHist
        (cofinalTailAgreementEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cofinalTailAgreementFields :
    CofinalTailAgreementUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CofinalTailAgreementUp.mk meet fusion budget sealRow dyadicRow readback handoff
      transport routes provenance name =>
      [meet, fusion, budget, sealRow, dyadicRow, readback, handoff, transport, routes,
        provenance, name]

def cofinalTailAgreementToEventFlow :
    CofinalTailAgreementUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cofinalTailAgreementFields x).map cofinalTailAgreementEncodeBHist

def cofinalTailAgreementFromEventFlow :
    EventFlow → Option CofinalTailAgreementUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | meet :: rest0 =>
      match rest0 with
      | [] => none
      | fusion :: rest1 =>
          match rest1 with
          | [] => none
          | budget :: rest2 =>
              match rest2 with
              | [] => none
              | sealRow :: rest3 =>
                  match rest3 with
                  | [] => none
                  | dyadicRow :: rest4 =>
                      match rest4 with
                      | [] => none
                      | readback :: rest5 =>
                          match rest5 with
                          | [] => none
                          | handoff :: rest6 =>
                              match rest6 with
                              | [] => none
                              | transport :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | routes :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | provenance :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | name :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (CofinalTailAgreementUp.mk
                                                      (cofinalTailAgreementDecodeBHist
                                                        meet)
                                                      (cofinalTailAgreementDecodeBHist
                                                        fusion)
                                                      (cofinalTailAgreementDecodeBHist
                                                        budget)
                                                      (cofinalTailAgreementDecodeBHist
                                                        sealRow)
                                                      (cofinalTailAgreementDecodeBHist
                                                        dyadicRow)
                                                      (cofinalTailAgreementDecodeBHist
                                                        readback)
                                                      (cofinalTailAgreementDecodeBHist
                                                        handoff)
                                                      (cofinalTailAgreementDecodeBHist
                                                        transport)
                                                      (cofinalTailAgreementDecodeBHist
                                                        routes)
                                                      (cofinalTailAgreementDecodeBHist
                                                        provenance)
                                                      (cofinalTailAgreementDecodeBHist
                                                        name))
                                              | _ :: _ => none

private theorem CofinalTailAgreementTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CofinalTailAgreementUp,
      cofinalTailAgreementFromEventFlow
        (cofinalTailAgreementToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk meet fusion budget sealRow dyadicRow readback handoff transport routes provenance
      name =>
      change
        some
          (CofinalTailAgreementUp.mk
            (cofinalTailAgreementDecodeBHist
              (cofinalTailAgreementEncodeBHist meet))
            (cofinalTailAgreementDecodeBHist
              (cofinalTailAgreementEncodeBHist fusion))
            (cofinalTailAgreementDecodeBHist
              (cofinalTailAgreementEncodeBHist budget))
            (cofinalTailAgreementDecodeBHist
              (cofinalTailAgreementEncodeBHist sealRow))
            (cofinalTailAgreementDecodeBHist
              (cofinalTailAgreementEncodeBHist dyadicRow))
            (cofinalTailAgreementDecodeBHist
              (cofinalTailAgreementEncodeBHist readback))
            (cofinalTailAgreementDecodeBHist
              (cofinalTailAgreementEncodeBHist handoff))
            (cofinalTailAgreementDecodeBHist
              (cofinalTailAgreementEncodeBHist transport))
            (cofinalTailAgreementDecodeBHist
              (cofinalTailAgreementEncodeBHist routes))
            (cofinalTailAgreementDecodeBHist
              (cofinalTailAgreementEncodeBHist provenance))
            (cofinalTailAgreementDecodeBHist
              (cofinalTailAgreementEncodeBHist name))) =
          some
            (CofinalTailAgreementUp.mk meet fusion budget sealRow dyadicRow readback
              handoff transport routes provenance name)
      rw [CofinalTailAgreementTasteGate_single_carrier_alignment_decode_encode meet,
        CofinalTailAgreementTasteGate_single_carrier_alignment_decode_encode fusion,
        CofinalTailAgreementTasteGate_single_carrier_alignment_decode_encode budget,
        CofinalTailAgreementTasteGate_single_carrier_alignment_decode_encode sealRow,
        CofinalTailAgreementTasteGate_single_carrier_alignment_decode_encode dyadicRow,
        CofinalTailAgreementTasteGate_single_carrier_alignment_decode_encode readback,
        CofinalTailAgreementTasteGate_single_carrier_alignment_decode_encode handoff,
        CofinalTailAgreementTasteGate_single_carrier_alignment_decode_encode transport,
        CofinalTailAgreementTasteGate_single_carrier_alignment_decode_encode routes,
        CofinalTailAgreementTasteGate_single_carrier_alignment_decode_encode provenance,
        CofinalTailAgreementTasteGate_single_carrier_alignment_decode_encode name]

private theorem CofinalTailAgreementTasteGate_single_carrier_alignment_injective
    {x y : CofinalTailAgreementUp} :
    cofinalTailAgreementToEventFlow x =
      cofinalTailAgreementToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cofinalTailAgreementFromEventFlow
          (cofinalTailAgreementToEventFlow x) =
        cofinalTailAgreementFromEventFlow
          (cofinalTailAgreementToEventFlow y) :=
    congrArg cofinalTailAgreementFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CofinalTailAgreementTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CofinalTailAgreementTasteGate_single_carrier_alignment_round_trip y)))

instance cofinalTailAgreementBHistCarrier :
    BHistCarrier CofinalTailAgreementUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cofinalTailAgreementToEventFlow
  fromEventFlow := cofinalTailAgreementFromEventFlow

instance cofinalTailAgreementChapterTasteGate :
    ChapterTasteGate CofinalTailAgreementUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cofinalTailAgreementFromEventFlow
        (cofinalTailAgreementToEventFlow x) = some x
    exact CofinalTailAgreementTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CofinalTailAgreementTasteGate_single_carrier_alignment_injective heq)

instance cofinalTailAgreementFieldFaithful :
    FieldFaithful CofinalTailAgreementUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cofinalTailAgreementFields
  field_faithful := by
    intro x y h
    cases x with
    | mk meet₁ fusion₁ budget₁ sealRow₁ dyadicRow₁ readback₁ handoff₁ transport₁ routes₁
        provenance₁ name₁ =>
        cases y with
        | mk meet₂ fusion₂ budget₂ sealRow₂ dyadicRow₂ readback₂ handoff₂ transport₂
            routes₂ provenance₂ name₂ =>
            injection h with hMeet hRest₁
            injection hRest₁ with hFusion hRest₂
            injection hRest₂ with hBudget hRest₃
            injection hRest₃ with hSealRowRow hRest₄
            injection hRest₄ with hDyadicRowRow hRest₅
            injection hRest₅ with hReadback hRest₆
            injection hRest₆ with hHandoff hRest₇
            injection hRest₇ with hTransport hRest₈
            injection hRest₈ with hRoutes hRest₉
            injection hRest₉ with hProvenance hRest₁₀
            injection hRest₁₀ with hName _
            subst hMeet
            subst hFusion
            subst hBudget
            subst hSealRowRow
            subst hDyadicRowRow
            subst hReadback
            subst hHandoff
            subst hTransport
            subst hRoutes
            subst hProvenance
            subst hName
            rfl

instance cofinalTailAgreementNontrivial :
    Nontrivial CofinalTailAgreementUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CofinalTailAgreementUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      CofinalTailAgreementUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CofinalTailAgreementUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cofinalTailAgreementChapterTasteGate

theorem CofinalTailAgreementTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cofinalTailAgreementDecodeBHist
        (cofinalTailAgreementEncodeBHist h) = h) ∧
      (∀ x : CofinalTailAgreementUp,
        cofinalTailAgreementFromEventFlow
          (cofinalTailAgreementToEventFlow x) = some x) ∧
        (∀ x y : CofinalTailAgreementUp,
          cofinalTailAgreementToEventFlow x =
            cofinalTailAgreementToEventFlow y → x = y) ∧
          cofinalTailAgreementEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact CofinalTailAgreementTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact CofinalTailAgreementTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact CofinalTailAgreementTasteGate_single_carrier_alignment_injective heq
      · rfl

end BEDC.Derived.CofinalTailAgreementUp
