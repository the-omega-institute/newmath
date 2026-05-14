import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DiagonalLimitBudgetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DiagonalLimitBudgetUp : Type where
  | mk :
      (request budget window dyadic sealRow transport continuation provenance name : BHist) →
        DiagonalLimitBudgetUp
  deriving DecidableEq

private def diagonalLimitBudgetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: diagonalLimitBudgetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: diagonalLimitBudgetEncodeBHist h

private def diagonalLimitBudgetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (diagonalLimitBudgetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (diagonalLimitBudgetDecodeBHist tail)

private theorem diagonalLimitBudgetDecodeEncodeBHist :
    ∀ h : BHist,
      diagonalLimitBudgetDecodeBHist (diagonalLimitBudgetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem diagonalLimitBudget_mk_congr
    {request request' budget budget' window window' dyadic dyadic' sealRow sealRow' transport
      transport' continuation continuation' provenance provenance' name name' : BHist}
    (hRequest : request' = request)
    (hBudget : budget' = budget)
    (hWindow : window' = window)
    (hDyadic : dyadic' = dyadic)
    (hSealRow : sealRow' = sealRow)
    (hTransport : transport' = transport)
    (hContinuation : continuation' = continuation)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    DiagonalLimitBudgetUp.mk request' budget' window' dyadic' sealRow' transport'
        continuation' provenance' name' =
      DiagonalLimitBudgetUp.mk request budget window dyadic sealRow transport continuation
        provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hRequest
  cases hBudget
  cases hWindow
  cases hDyadic
  cases hSealRow
  cases hTransport
  cases hContinuation
  cases hProvenance
  cases hName
  rfl

private def diagonalLimitBudgetToEventFlow : DiagonalLimitBudgetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | DiagonalLimitBudgetUp.mk request budget window dyadic sealRow transport continuation
      provenance name =>
      [[BMark.b0],
        diagonalLimitBudgetEncodeBHist request,
        [BMark.b1, BMark.b0],
        diagonalLimitBudgetEncodeBHist budget,
        [BMark.b1, BMark.b1, BMark.b0],
        diagonalLimitBudgetEncodeBHist window,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        diagonalLimitBudgetEncodeBHist dyadic,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        diagonalLimitBudgetEncodeBHist sealRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        diagonalLimitBudgetEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        diagonalLimitBudgetEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        diagonalLimitBudgetEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        diagonalLimitBudgetEncodeBHist name]

private def diagonalLimitBudgetFromEventFlow :
    EventFlow → Option DiagonalLimitBudgetUp
  -- BEDC touchpoint anchor: BHist BMark
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
              | budget :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | window :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | dyadic :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | sealRow :: rest9 =>
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
                                                      | continuation :: rest13 =>
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
                                                                                (DiagonalLimitBudgetUp.mk
                                                                                  (diagonalLimitBudgetDecodeBHist
                                                                                    request)
                                                                                  (diagonalLimitBudgetDecodeBHist
                                                                                    budget)
                                                                                  (diagonalLimitBudgetDecodeBHist
                                                                                    window)
                                                                                  (diagonalLimitBudgetDecodeBHist
                                                                                    dyadic)
                                                                                  (diagonalLimitBudgetDecodeBHist
                                                                                    sealRow)
                                                                                  (diagonalLimitBudgetDecodeBHist
                                                                                    transport)
                                                                                  (diagonalLimitBudgetDecodeBHist
                                                                                    continuation)
                                                                                  (diagonalLimitBudgetDecodeBHist
                                                                                    provenance)
                                                                                  (diagonalLimitBudgetDecodeBHist
                                                                                    name))
                                                                          | _ :: _ => none

private theorem diagonalLimitBudgetRoundTrip :
    ∀ x : DiagonalLimitBudgetUp,
      diagonalLimitBudgetFromEventFlow (diagonalLimitBudgetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk request budget window dyadic sealRow transport continuation provenance name =>
      change
        some
          (DiagonalLimitBudgetUp.mk
            (diagonalLimitBudgetDecodeBHist (diagonalLimitBudgetEncodeBHist request))
            (diagonalLimitBudgetDecodeBHist (diagonalLimitBudgetEncodeBHist budget))
            (diagonalLimitBudgetDecodeBHist (diagonalLimitBudgetEncodeBHist window))
            (diagonalLimitBudgetDecodeBHist (diagonalLimitBudgetEncodeBHist dyadic))
            (diagonalLimitBudgetDecodeBHist (diagonalLimitBudgetEncodeBHist sealRow))
            (diagonalLimitBudgetDecodeBHist (diagonalLimitBudgetEncodeBHist transport))
            (diagonalLimitBudgetDecodeBHist (diagonalLimitBudgetEncodeBHist continuation))
            (diagonalLimitBudgetDecodeBHist (diagonalLimitBudgetEncodeBHist provenance))
            (diagonalLimitBudgetDecodeBHist (diagonalLimitBudgetEncodeBHist name))) =
          some
            (DiagonalLimitBudgetUp.mk request budget window dyadic sealRow transport continuation
              provenance name)
      exact
        congrArg some
          (diagonalLimitBudget_mk_congr
            (diagonalLimitBudgetDecodeEncodeBHist request)
            (diagonalLimitBudgetDecodeEncodeBHist budget)
            (diagonalLimitBudgetDecodeEncodeBHist window)
            (diagonalLimitBudgetDecodeEncodeBHist dyadic)
            (diagonalLimitBudgetDecodeEncodeBHist sealRow)
            (diagonalLimitBudgetDecodeEncodeBHist transport)
            (diagonalLimitBudgetDecodeEncodeBHist continuation)
            (diagonalLimitBudgetDecodeEncodeBHist provenance)
            (diagonalLimitBudgetDecodeEncodeBHist name))

private theorem diagonalLimitBudgetToEventFlow_injective
    {x y : DiagonalLimitBudgetUp} :
    diagonalLimitBudgetToEventFlow x = diagonalLimitBudgetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      diagonalLimitBudgetFromEventFlow (diagonalLimitBudgetToEventFlow x) =
        diagonalLimitBudgetFromEventFlow (diagonalLimitBudgetToEventFlow y) :=
    congrArg diagonalLimitBudgetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (diagonalLimitBudgetRoundTrip x).symm
      (Eq.trans hread (diagonalLimitBudgetRoundTrip y)))

private def diagonalLimitBudgetFields : DiagonalLimitBudgetUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DiagonalLimitBudgetUp.mk request budget window dyadic sealRow transport continuation
      provenance name =>
      [request, budget, window, dyadic, sealRow, transport, continuation, provenance, name]

private theorem diagonalLimitBudget_field_faithful :
    ∀ x y : DiagonalLimitBudgetUp,
      diagonalLimitBudgetFields x = diagonalLimitBudgetFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk request budget window dyadic sealRow transport continuation provenance name =>
      cases y with
      | mk request' budget' window' dyadic' sealRow' transport' continuation' provenance'
          name' =>
          cases hfields
          rfl

instance diagonalLimitBudgetBHistCarrier : BHistCarrier DiagonalLimitBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := diagonalLimitBudgetToEventFlow
  fromEventFlow := diagonalLimitBudgetFromEventFlow

instance diagonalLimitBudgetChapterTasteGate :
    ChapterTasteGate DiagonalLimitBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change diagonalLimitBudgetFromEventFlow (diagonalLimitBudgetToEventFlow x) = some x
    exact diagonalLimitBudgetRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (diagonalLimitBudgetToEventFlow_injective heq)

instance diagonalLimitBudgetFieldFaithful : FieldFaithful DiagonalLimitBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := diagonalLimitBudgetFields
  field_faithful := diagonalLimitBudget_field_faithful

instance diagonalLimitBudgetNontrivial : Nontrivial DiagonalLimitBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DiagonalLimitBudgetUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DiagonalLimitBudgetUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DiagonalLimitBudgetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  diagonalLimitBudgetChapterTasteGate

theorem DiagonalLimitBudgetTasteGate_single_carrier_alignment :
    (∀ h : BHist, diagonalLimitBudgetDecodeBHist
        (diagonalLimitBudgetEncodeBHist h) = h) ∧
      (∀ x : DiagonalLimitBudgetUp,
        diagonalLimitBudgetFromEventFlow (diagonalLimitBudgetToEventFlow x) = some x) ∧
        (∀ x y : DiagonalLimitBudgetUp,
          diagonalLimitBudgetToEventFlow x = diagonalLimitBudgetToEventFlow y → x = y) ∧
          diagonalLimitBudgetEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact diagonalLimitBudgetDecodeEncodeBHist
  · constructor
    · exact diagonalLimitBudgetRoundTrip
    · constructor
      · intro x y heq
        exact diagonalLimitBudgetToEventFlow_injective heq
      · rfl

end BEDC.Derived.DiagonalLimitBudgetUp
