import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.InterHistSymmetryBudgetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive InterHistSymmetryBudgetUp : Type where
  | mk
      (sourceLeft sourceRight localityAB localityBA observerCell invariantReadback
        noGlobalSync transport continuation provenance nameCert : BHist) :
      InterHistSymmetryBudgetUp
  deriving DecidableEq

private def interHistSymmetryBudgetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: interHistSymmetryBudgetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: interHistSymmetryBudgetEncodeBHist h

private def interHistSymmetryBudgetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (interHistSymmetryBudgetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (interHistSymmetryBudgetDecodeBHist tail)

private theorem interHistSymmetryBudgetDecode_encode_bhist :
    ∀ h : BHist,
      interHistSymmetryBudgetDecodeBHist
        (interHistSymmetryBudgetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem interHistSymmetryBudget_mk_congr
    {sourceLeft sourceLeft' sourceRight sourceRight' localityAB localityAB'
      localityBA localityBA' observerCell observerCell' invariantReadback
      invariantReadback' noGlobalSync noGlobalSync' transport transport'
      continuation continuation' provenance provenance' nameCert nameCert' : BHist}
    (hSourceLeft : sourceLeft' = sourceLeft)
    (hSourceRight : sourceRight' = sourceRight)
    (hLocalityAB : localityAB' = localityAB)
    (hLocalityBA : localityBA' = localityBA)
    (hObserverCell : observerCell' = observerCell)
    (hInvariantReadback : invariantReadback' = invariantReadback)
    (hNoGlobalSync : noGlobalSync' = noGlobalSync)
    (hTransport : transport' = transport)
    (hContinuation : continuation' = continuation)
    (hProvenance : provenance' = provenance)
    (hNameCert : nameCert' = nameCert) :
    InterHistSymmetryBudgetUp.mk sourceLeft' sourceRight' localityAB' localityBA'
        observerCell' invariantReadback' noGlobalSync' transport' continuation'
        provenance' nameCert' =
      InterHistSymmetryBudgetUp.mk sourceLeft sourceRight localityAB localityBA
        observerCell invariantReadback noGlobalSync transport continuation provenance
        nameCert := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hSourceLeft
  cases hSourceRight
  cases hLocalityAB
  cases hLocalityBA
  cases hObserverCell
  cases hInvariantReadback
  cases hNoGlobalSync
  cases hTransport
  cases hContinuation
  cases hProvenance
  cases hNameCert
  rfl

private def interHistSymmetryBudgetToEventFlow :
    InterHistSymmetryBudgetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | InterHistSymmetryBudgetUp.mk sourceLeft sourceRight localityAB localityBA
      observerCell invariantReadback noGlobalSync transport continuation provenance
      nameCert =>
      [[BMark.b0],
        interHistSymmetryBudgetEncodeBHist sourceLeft,
        [BMark.b1, BMark.b0],
        interHistSymmetryBudgetEncodeBHist sourceRight,
        [BMark.b1, BMark.b1, BMark.b0],
        interHistSymmetryBudgetEncodeBHist localityAB,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        interHistSymmetryBudgetEncodeBHist localityBA,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        interHistSymmetryBudgetEncodeBHist observerCell,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        interHistSymmetryBudgetEncodeBHist invariantReadback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        interHistSymmetryBudgetEncodeBHist noGlobalSync,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        interHistSymmetryBudgetEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        interHistSymmetryBudgetEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        interHistSymmetryBudgetEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        interHistSymmetryBudgetEncodeBHist nameCert]

private def interHistSymmetryBudgetFromEventFlow :
    EventFlow → Option InterHistSymmetryBudgetUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | sourceLeft :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | sourceRight :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | localityAB :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | localityBA :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | observerCell :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | invariantReadback :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | noGlobalSync :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | transport :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | continuation :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | provenance :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | nameCert :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] =>
                                                                                              some
                                                                                                (InterHistSymmetryBudgetUp.mk
                                                                                                  (interHistSymmetryBudgetDecodeBHist sourceLeft)
                                                                                                  (interHistSymmetryBudgetDecodeBHist sourceRight)
                                                                                                  (interHistSymmetryBudgetDecodeBHist localityAB)
                                                                                                  (interHistSymmetryBudgetDecodeBHist localityBA)
                                                                                                  (interHistSymmetryBudgetDecodeBHist observerCell)
                                                                                                  (interHistSymmetryBudgetDecodeBHist invariantReadback)
                                                                                                  (interHistSymmetryBudgetDecodeBHist noGlobalSync)
                                                                                                  (interHistSymmetryBudgetDecodeBHist transport)
                                                                                                  (interHistSymmetryBudgetDecodeBHist continuation)
                                                                                                  (interHistSymmetryBudgetDecodeBHist provenance)
                                                                                                  (interHistSymmetryBudgetDecodeBHist nameCert))
                                                                                          | _ :: _ => none

private theorem interHistSymmetryBudget_round_trip :
    ∀ x : InterHistSymmetryBudgetUp,
      interHistSymmetryBudgetFromEventFlow
        (interHistSymmetryBudgetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk sourceLeft sourceRight localityAB localityBA observerCell invariantReadback
      noGlobalSync transport continuation provenance nameCert =>
      change
        some
          (InterHistSymmetryBudgetUp.mk
            (interHistSymmetryBudgetDecodeBHist
              (interHistSymmetryBudgetEncodeBHist sourceLeft))
            (interHistSymmetryBudgetDecodeBHist
              (interHistSymmetryBudgetEncodeBHist sourceRight))
            (interHistSymmetryBudgetDecodeBHist
              (interHistSymmetryBudgetEncodeBHist localityAB))
            (interHistSymmetryBudgetDecodeBHist
              (interHistSymmetryBudgetEncodeBHist localityBA))
            (interHistSymmetryBudgetDecodeBHist
              (interHistSymmetryBudgetEncodeBHist observerCell))
            (interHistSymmetryBudgetDecodeBHist
              (interHistSymmetryBudgetEncodeBHist invariantReadback))
            (interHistSymmetryBudgetDecodeBHist
              (interHistSymmetryBudgetEncodeBHist noGlobalSync))
            (interHistSymmetryBudgetDecodeBHist
              (interHistSymmetryBudgetEncodeBHist transport))
            (interHistSymmetryBudgetDecodeBHist
              (interHistSymmetryBudgetEncodeBHist continuation))
            (interHistSymmetryBudgetDecodeBHist
              (interHistSymmetryBudgetEncodeBHist provenance))
            (interHistSymmetryBudgetDecodeBHist
              (interHistSymmetryBudgetEncodeBHist nameCert))) =
          some
            (InterHistSymmetryBudgetUp.mk sourceLeft sourceRight localityAB
              localityBA observerCell invariantReadback noGlobalSync transport
              continuation provenance nameCert)
      exact
        congrArg some
          (interHistSymmetryBudget_mk_congr
            (interHistSymmetryBudgetDecode_encode_bhist sourceLeft)
            (interHistSymmetryBudgetDecode_encode_bhist sourceRight)
            (interHistSymmetryBudgetDecode_encode_bhist localityAB)
            (interHistSymmetryBudgetDecode_encode_bhist localityBA)
            (interHistSymmetryBudgetDecode_encode_bhist observerCell)
            (interHistSymmetryBudgetDecode_encode_bhist invariantReadback)
            (interHistSymmetryBudgetDecode_encode_bhist noGlobalSync)
            (interHistSymmetryBudgetDecode_encode_bhist transport)
            (interHistSymmetryBudgetDecode_encode_bhist continuation)
            (interHistSymmetryBudgetDecode_encode_bhist provenance)
            (interHistSymmetryBudgetDecode_encode_bhist nameCert))

private theorem interHistSymmetryBudgetToEventFlow_injective
    {x y : InterHistSymmetryBudgetUp} :
    interHistSymmetryBudgetToEventFlow x =
      interHistSymmetryBudgetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      interHistSymmetryBudgetFromEventFlow
          (interHistSymmetryBudgetToEventFlow x) =
        interHistSymmetryBudgetFromEventFlow
          (interHistSymmetryBudgetToEventFlow y) :=
    congrArg interHistSymmetryBudgetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (interHistSymmetryBudget_round_trip x).symm
      (Eq.trans hread (interHistSymmetryBudget_round_trip y)))

instance interHistSymmetryBudgetBHistCarrier :
    BHistCarrier InterHistSymmetryBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := interHistSymmetryBudgetToEventFlow
  fromEventFlow := interHistSymmetryBudgetFromEventFlow

instance interHistSymmetryBudgetChapterTasteGate :
    ChapterTasteGate InterHistSymmetryBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      interHistSymmetryBudgetFromEventFlow
        (interHistSymmetryBudgetToEventFlow x) = some x
    exact interHistSymmetryBudget_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (interHistSymmetryBudgetToEventFlow_injective heq)

def taste_gate : ChapterTasteGate InterHistSymmetryBudgetUp :=
  interHistSymmetryBudgetChapterTasteGate

instance interHistSymmetryBudgetFieldFaithful :
    FieldFaithful InterHistSymmetryBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | InterHistSymmetryBudgetUp.mk sourceLeft sourceRight localityAB localityBA
        observerCell invariantReadback noGlobalSync transport continuation provenance
        nameCert =>
        [sourceLeft, sourceRight, localityAB, localityBA, observerCell,
          invariantReadback, noGlobalSync, transport, continuation, provenance,
          nameCert]
  field_faithful := by
    intro x y hfields
    cases x with
    | mk sourceLeft sourceRight localityAB localityBA observerCell invariantReadback
        noGlobalSync transport continuation provenance nameCert =>
        cases y with
        | mk sourceLeft' sourceRight' localityAB' localityBA' observerCell'
            invariantReadback' noGlobalSync' transport' continuation' provenance'
            nameCert' =>
            cases hfields
            rfl

instance interHistSymmetryBudgetNontrivial :
    Nontrivial InterHistSymmetryBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨InterHistSymmetryBudgetUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      InterHistSymmetryBudgetUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem InterHistSymmetryBudgetTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      interHistSymmetryBudgetDecodeBHist
        (interHistSymmetryBudgetEncodeBHist h) = h) ∧
      (∀ x : InterHistSymmetryBudgetUp,
        interHistSymmetryBudgetFromEventFlow
          (interHistSymmetryBudgetToEventFlow x) = some x) ∧
        (∀ x y : InterHistSymmetryBudgetUp,
          interHistSymmetryBudgetToEventFlow x =
            interHistSymmetryBudgetToEventFlow y → x = y) ∧
          interHistSymmetryBudgetEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact interHistSymmetryBudgetDecode_encode_bhist
  · constructor
    · exact interHistSymmetryBudget_round_trip
    · constructor
      · intro x y heq
        exact interHistSymmetryBudgetToEventFlow_injective heq
      · rfl

end BEDC.Derived.InterHistSymmetryBudgetUp
