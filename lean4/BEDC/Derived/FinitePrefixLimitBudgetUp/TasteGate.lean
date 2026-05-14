import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FinitePrefixLimitBudgetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FinitePrefixLimitBudgetUp : Type where
  | mk :
      (request budget window depth readback sealRow exclusion transport routes provenance
        name : BHist) →
      FinitePrefixLimitBudgetUp
  deriving DecidableEq

def finitePrefixLimitBudgetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finitePrefixLimitBudgetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finitePrefixLimitBudgetEncodeBHist h

def finitePrefixLimitBudgetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finitePrefixLimitBudgetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finitePrefixLimitBudgetDecodeBHist tail)

private theorem FinitePrefixLimitBudgetTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      finitePrefixLimitBudgetDecodeBHist
        (finitePrefixLimitBudgetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def finitePrefixLimitBudgetFields :
    FinitePrefixLimitBudgetUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FinitePrefixLimitBudgetUp.mk request budget window depth readback sealRow exclusion
      transport routes provenance name =>
      [request, budget, window, depth, readback, sealRow, exclusion, transport, routes,
        provenance, name]

def finitePrefixLimitBudgetToEventFlow :
    FinitePrefixLimitBudgetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (finitePrefixLimitBudgetFields x).map finitePrefixLimitBudgetEncodeBHist

def finitePrefixLimitBudgetFromEventFlow :
    EventFlow → Option FinitePrefixLimitBudgetUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | request :: rest0 =>
      match rest0 with
      | [] => none
      | budget :: rest1 =>
          match rest1 with
          | [] => none
          | window :: rest2 =>
              match rest2 with
              | [] => none
              | depth :: rest3 =>
                  match rest3 with
                  | [] => none
                  | readback :: rest4 =>
                      match rest4 with
                      | [] => none
                      | sealRow :: rest5 =>
                          match rest5 with
                          | [] => none
                          | exclusion :: rest6 =>
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
                                                    (FinitePrefixLimitBudgetUp.mk
                                                      (finitePrefixLimitBudgetDecodeBHist
                                                        request)
                                                      (finitePrefixLimitBudgetDecodeBHist
                                                        budget)
                                                      (finitePrefixLimitBudgetDecodeBHist
                                                        window)
                                                      (finitePrefixLimitBudgetDecodeBHist
                                                        depth)
                                                      (finitePrefixLimitBudgetDecodeBHist
                                                        readback)
                                                      (finitePrefixLimitBudgetDecodeBHist
                                                        sealRow)
                                                      (finitePrefixLimitBudgetDecodeBHist
                                                        exclusion)
                                                      (finitePrefixLimitBudgetDecodeBHist
                                                        transport)
                                                      (finitePrefixLimitBudgetDecodeBHist
                                                        routes)
                                                      (finitePrefixLimitBudgetDecodeBHist
                                                        provenance)
                                                      (finitePrefixLimitBudgetDecodeBHist
                                                        name))
                                              | _ :: _ => none

private theorem FinitePrefixLimitBudgetTasteGate_single_carrier_alignment_round_trip :
    ∀ x : FinitePrefixLimitBudgetUp,
      finitePrefixLimitBudgetFromEventFlow
        (finitePrefixLimitBudgetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk request budget window depth readback sealRow exclusion transport routes provenance
      name =>
      change
        some
          (FinitePrefixLimitBudgetUp.mk
            (finitePrefixLimitBudgetDecodeBHist
              (finitePrefixLimitBudgetEncodeBHist request))
            (finitePrefixLimitBudgetDecodeBHist
              (finitePrefixLimitBudgetEncodeBHist budget))
            (finitePrefixLimitBudgetDecodeBHist
              (finitePrefixLimitBudgetEncodeBHist window))
            (finitePrefixLimitBudgetDecodeBHist
              (finitePrefixLimitBudgetEncodeBHist depth))
            (finitePrefixLimitBudgetDecodeBHist
              (finitePrefixLimitBudgetEncodeBHist readback))
            (finitePrefixLimitBudgetDecodeBHist
              (finitePrefixLimitBudgetEncodeBHist sealRow))
            (finitePrefixLimitBudgetDecodeBHist
              (finitePrefixLimitBudgetEncodeBHist exclusion))
            (finitePrefixLimitBudgetDecodeBHist
              (finitePrefixLimitBudgetEncodeBHist transport))
            (finitePrefixLimitBudgetDecodeBHist
              (finitePrefixLimitBudgetEncodeBHist routes))
            (finitePrefixLimitBudgetDecodeBHist
              (finitePrefixLimitBudgetEncodeBHist provenance))
            (finitePrefixLimitBudgetDecodeBHist
              (finitePrefixLimitBudgetEncodeBHist name))) =
          some
            (FinitePrefixLimitBudgetUp.mk request budget window depth readback sealRow
              exclusion transport routes provenance name)
      rw [FinitePrefixLimitBudgetTasteGate_single_carrier_alignment_decode_encode
          request,
        FinitePrefixLimitBudgetTasteGate_single_carrier_alignment_decode_encode
          budget,
        FinitePrefixLimitBudgetTasteGate_single_carrier_alignment_decode_encode
          window,
        FinitePrefixLimitBudgetTasteGate_single_carrier_alignment_decode_encode
          depth,
        FinitePrefixLimitBudgetTasteGate_single_carrier_alignment_decode_encode
          readback,
        FinitePrefixLimitBudgetTasteGate_single_carrier_alignment_decode_encode
          sealRow,
        FinitePrefixLimitBudgetTasteGate_single_carrier_alignment_decode_encode
          exclusion,
        FinitePrefixLimitBudgetTasteGate_single_carrier_alignment_decode_encode
          transport,
        FinitePrefixLimitBudgetTasteGate_single_carrier_alignment_decode_encode
          routes,
        FinitePrefixLimitBudgetTasteGate_single_carrier_alignment_decode_encode
          provenance,
        FinitePrefixLimitBudgetTasteGate_single_carrier_alignment_decode_encode
          name]

private theorem FinitePrefixLimitBudgetTasteGate_single_carrier_alignment_injective
    {x y : FinitePrefixLimitBudgetUp} :
    finitePrefixLimitBudgetToEventFlow x =
      finitePrefixLimitBudgetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finitePrefixLimitBudgetFromEventFlow
          (finitePrefixLimitBudgetToEventFlow x) =
        finitePrefixLimitBudgetFromEventFlow
          (finitePrefixLimitBudgetToEventFlow y) :=
    congrArg finitePrefixLimitBudgetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (FinitePrefixLimitBudgetTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (FinitePrefixLimitBudgetTasteGate_single_carrier_alignment_round_trip y)))

instance finitePrefixLimitBudgetBHistCarrier :
    BHistCarrier FinitePrefixLimitBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finitePrefixLimitBudgetToEventFlow
  fromEventFlow := finitePrefixLimitBudgetFromEventFlow

instance finitePrefixLimitBudgetChapterTasteGate :
    ChapterTasteGate FinitePrefixLimitBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      finitePrefixLimitBudgetFromEventFlow
        (finitePrefixLimitBudgetToEventFlow x) = some x
    exact FinitePrefixLimitBudgetTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FinitePrefixLimitBudgetTasteGate_single_carrier_alignment_injective heq)

instance finitePrefixLimitBudgetFieldFaithful :
    FieldFaithful FinitePrefixLimitBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finitePrefixLimitBudgetFields
  field_faithful := by
    intro x y h
    cases x with
    | mk request₁ budget₁ window₁ depth₁ readback₁ sealRow₁ exclusion₁ transport₁
        routes₁ provenance₁ name₁ =>
        cases y with
        | mk request₂ budget₂ window₂ depth₂ readback₂ sealRow₂ exclusion₂ transport₂
            routes₂ provenance₂ name₂ =>
            injection h with hRequest hRest₁
            injection hRest₁ with hBudget hRest₂
            injection hRest₂ with hWindow hRest₃
            injection hRest₃ with hDepth hRest₄
            injection hRest₄ with hReadback hRest₅
            injection hRest₅ with hSealRowRow hRest₆
            injection hRest₆ with hExclusion hRest₇
            injection hRest₇ with hTransport hRest₈
            injection hRest₈ with hRoutes hRest₉
            injection hRest₉ with hProvenance hRest₁₀
            injection hRest₁₀ with hName _
            subst hRequest
            subst hBudget
            subst hWindow
            subst hDepth
            subst hReadback
            subst hSealRowRow
            subst hExclusion
            subst hTransport
            subst hRoutes
            subst hProvenance
            subst hName
            rfl

instance finitePrefixLimitBudgetNontrivial :
    Nontrivial FinitePrefixLimitBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FinitePrefixLimitBudgetUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      FinitePrefixLimitBudgetUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FinitePrefixLimitBudgetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finitePrefixLimitBudgetChapterTasteGate

theorem FinitePrefixLimitBudgetTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      finitePrefixLimitBudgetDecodeBHist
        (finitePrefixLimitBudgetEncodeBHist h) = h) ∧
      (∀ x : FinitePrefixLimitBudgetUp,
        finitePrefixLimitBudgetFromEventFlow
          (finitePrefixLimitBudgetToEventFlow x) = some x) ∧
        (∀ x y : FinitePrefixLimitBudgetUp,
          finitePrefixLimitBudgetToEventFlow x =
            finitePrefixLimitBudgetToEventFlow y → x = y) ∧
          finitePrefixLimitBudgetEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact FinitePrefixLimitBudgetTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact FinitePrefixLimitBudgetTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact FinitePrefixLimitBudgetTasteGate_single_carrier_alignment_injective heq
      · rfl

end BEDC.Derived.FinitePrefixLimitBudgetUp
