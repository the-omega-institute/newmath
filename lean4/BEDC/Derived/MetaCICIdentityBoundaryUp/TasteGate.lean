import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaCICIdentityBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaCICIdentityBoundaryUp : Type where
  | mk :
      (generators equality recursors purity boundary ledger handoff classifier name cert :
        BHist) →
      MetaCICIdentityBoundaryUp
  deriving DecidableEq

def metaCICIdentityBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metaCICIdentityBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metaCICIdentityBoundaryEncodeBHist h

def metaCICIdentityBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metaCICIdentityBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metaCICIdentityBoundaryDecodeBHist tail)

private theorem metaCICIdentityBoundary_decode_encode_bhist :
    ∀ h : BHist,
      metaCICIdentityBoundaryDecodeBHist (metaCICIdentityBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def metaCICIdentityBoundaryToEventFlow : MetaCICIdentityBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICIdentityBoundaryUp.mk generators equality recursors purity boundary ledger handoff
      classifier name cert =>
      [[BMark.b0],
        metaCICIdentityBoundaryEncodeBHist generators,
        [BMark.b1, BMark.b0],
        metaCICIdentityBoundaryEncodeBHist equality,
        [BMark.b1, BMark.b1, BMark.b0],
        metaCICIdentityBoundaryEncodeBHist recursors,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICIdentityBoundaryEncodeBHist purity,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICIdentityBoundaryEncodeBHist boundary,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICIdentityBoundaryEncodeBHist ledger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICIdentityBoundaryEncodeBHist handoff,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        metaCICIdentityBoundaryEncodeBHist classifier,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        metaCICIdentityBoundaryEncodeBHist name,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        metaCICIdentityBoundaryEncodeBHist cert]

def metaCICIdentityBoundaryFromEventFlow :
    EventFlow → Option MetaCICIdentityBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | generators :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | equality :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | recursors :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | purity :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | boundary :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | ledger :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | handoff :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | classifier :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | name :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | cert :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      some
                                                                                        (MetaCICIdentityBoundaryUp.mk
                                                                                          (metaCICIdentityBoundaryDecodeBHist
                                                                                            generators)
                                                                                          (metaCICIdentityBoundaryDecodeBHist
                                                                                            equality)
                                                                                          (metaCICIdentityBoundaryDecodeBHist
                                                                                            recursors)
                                                                                          (metaCICIdentityBoundaryDecodeBHist
                                                                                            purity)
                                                                                          (metaCICIdentityBoundaryDecodeBHist
                                                                                            boundary)
                                                                                          (metaCICIdentityBoundaryDecodeBHist
                                                                                            ledger)
                                                                                          (metaCICIdentityBoundaryDecodeBHist
                                                                                            handoff)
                                                                                          (metaCICIdentityBoundaryDecodeBHist
                                                                                            classifier)
                                                                                          (metaCICIdentityBoundaryDecodeBHist
                                                                                            name)
                                                                                          (metaCICIdentityBoundaryDecodeBHist
                                                                                            cert))
                                                                                  | _ :: _ => none

private theorem metaCICIdentityBoundary_round_trip :
    ∀ x : MetaCICIdentityBoundaryUp,
      metaCICIdentityBoundaryFromEventFlow (metaCICIdentityBoundaryToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk generators equality recursors purity boundary ledger handoff classifier name cert =>
      change
        some
          (MetaCICIdentityBoundaryUp.mk
            (metaCICIdentityBoundaryDecodeBHist
              (metaCICIdentityBoundaryEncodeBHist generators))
            (metaCICIdentityBoundaryDecodeBHist
              (metaCICIdentityBoundaryEncodeBHist equality))
            (metaCICIdentityBoundaryDecodeBHist
              (metaCICIdentityBoundaryEncodeBHist recursors))
            (metaCICIdentityBoundaryDecodeBHist
              (metaCICIdentityBoundaryEncodeBHist purity))
            (metaCICIdentityBoundaryDecodeBHist
              (metaCICIdentityBoundaryEncodeBHist boundary))
            (metaCICIdentityBoundaryDecodeBHist
              (metaCICIdentityBoundaryEncodeBHist ledger))
            (metaCICIdentityBoundaryDecodeBHist
              (metaCICIdentityBoundaryEncodeBHist handoff))
            (metaCICIdentityBoundaryDecodeBHist
              (metaCICIdentityBoundaryEncodeBHist classifier))
            (metaCICIdentityBoundaryDecodeBHist
              (metaCICIdentityBoundaryEncodeBHist name))
            (metaCICIdentityBoundaryDecodeBHist
              (metaCICIdentityBoundaryEncodeBHist cert))) =
          some
            (MetaCICIdentityBoundaryUp.mk generators equality recursors purity boundary ledger
              handoff classifier name cert)
      rw [metaCICIdentityBoundary_decode_encode_bhist generators,
        metaCICIdentityBoundary_decode_encode_bhist equality,
        metaCICIdentityBoundary_decode_encode_bhist recursors,
        metaCICIdentityBoundary_decode_encode_bhist purity,
        metaCICIdentityBoundary_decode_encode_bhist boundary,
        metaCICIdentityBoundary_decode_encode_bhist ledger,
        metaCICIdentityBoundary_decode_encode_bhist handoff,
        metaCICIdentityBoundary_decode_encode_bhist classifier,
        metaCICIdentityBoundary_decode_encode_bhist name,
        metaCICIdentityBoundary_decode_encode_bhist cert]

private theorem metaCICIdentityBoundaryToEventFlow_injective
    {x y : MetaCICIdentityBoundaryUp} :
    metaCICIdentityBoundaryToEventFlow x = metaCICIdentityBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metaCICIdentityBoundaryFromEventFlow (metaCICIdentityBoundaryToEventFlow x) =
        metaCICIdentityBoundaryFromEventFlow (metaCICIdentityBoundaryToEventFlow y) :=
    congrArg metaCICIdentityBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metaCICIdentityBoundary_round_trip x).symm
      (Eq.trans hread (metaCICIdentityBoundary_round_trip y)))

instance metaCICIdentityBoundaryBHistCarrier :
    BHistCarrier MetaCICIdentityBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metaCICIdentityBoundaryToEventFlow
  fromEventFlow := metaCICIdentityBoundaryFromEventFlow

instance metaCICIdentityBoundaryChapterTasteGate :
    ChapterTasteGate MetaCICIdentityBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change metaCICIdentityBoundaryFromEventFlow (metaCICIdentityBoundaryToEventFlow x) =
      some x
    exact metaCICIdentityBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metaCICIdentityBoundaryToEventFlow_injective heq)

instance metaCICIdentityBoundaryFieldFaithful :
    FieldFaithful MetaCICIdentityBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | MetaCICIdentityBoundaryUp.mk generators equality recursors purity boundary ledger
        handoff classifier name cert =>
        [generators, equality, recursors, purity, boundary, ledger, handoff, classifier, name,
          cert]
  field_faithful := by
    intro x y h
    cases x with
    | mk generators₁ equality₁ recursors₁ purity₁ boundary₁ ledger₁ handoff₁ classifier₁ name₁
        cert₁ =>
        cases y with
        | mk generators₂ equality₂ recursors₂ purity₂ boundary₂ ledger₂ handoff₂ classifier₂
            name₂ cert₂ =>
            simp only [] at h
            injection h with hGenerators hRest₁
            injection hRest₁ with hEquality hRest₂
            injection hRest₂ with hRecursors hRest₃
            injection hRest₃ with hPurity hRest₄
            injection hRest₄ with hBoundary hRest₅
            injection hRest₅ with hLedger hRest₆
            injection hRest₆ with hHandoff hRest₇
            injection hRest₇ with hClassifier hRest₈
            injection hRest₈ with hName hRest₉
            injection hRest₉ with hCert _
            subst hGenerators
            subst hEquality
            subst hRecursors
            subst hPurity
            subst hBoundary
            subst hLedger
            subst hHandoff
            subst hClassifier
            subst hName
            subst hCert
            rfl

instance metaCICIdentityBoundaryNontrivial :
    Nontrivial MetaCICIdentityBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MetaCICIdentityBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MetaCICIdentityBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem MetaCICIdentityBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist, metaCICIdentityBoundaryDecodeBHist
      (metaCICIdentityBoundaryEncodeBHist h) = h) ∧
      (∀ x : MetaCICIdentityBoundaryUp,
        metaCICIdentityBoundaryFromEventFlow (metaCICIdentityBoundaryToEventFlow x) =
          some x) ∧
        (∀ x y : MetaCICIdentityBoundaryUp,
          metaCICIdentityBoundaryToEventFlow x = metaCICIdentityBoundaryToEventFlow y ->
            x = y) ∧
          metaCICIdentityBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact metaCICIdentityBoundary_decode_encode_bhist
  · constructor
    · exact metaCICIdentityBoundary_round_trip
    · constructor
      · intro x y heq
        exact metaCICIdentityBoundaryToEventFlow_injective heq
      · rfl

end BEDC.Derived.MetaCICIdentityBoundaryUp
