import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FullAxisUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FullAxisUp : Type where
  | mk :
      (prefixThread source boundary classifier stability ledger provenance name : BHist) →
        FullAxisUp
  deriving DecidableEq

def FullAxisUp_completion_sibling_separation_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: FullAxisUp_completion_sibling_separation_encodeBHist h
  | BHist.e1 h => BMark.b1 :: FullAxisUp_completion_sibling_separation_encodeBHist h

def FullAxisUp_completion_sibling_separation_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (FullAxisUp_completion_sibling_separation_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (FullAxisUp_completion_sibling_separation_decodeBHist tail)

private theorem FullAxisUp_completion_sibling_separation_decode_encode_bhist :
    ∀ h : BHist,
      FullAxisUp_completion_sibling_separation_decodeBHist
          (FullAxisUp_completion_sibling_separation_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def FullAxisUp_completion_sibling_separation_toEventFlow : FullAxisUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FullAxisUp.mk prefixThread source boundary classifier stability ledger provenance name =>
      [[BMark.b0],
        FullAxisUp_completion_sibling_separation_encodeBHist prefixThread,
        [BMark.b1, BMark.b0],
        FullAxisUp_completion_sibling_separation_encodeBHist source,
        [BMark.b1, BMark.b1, BMark.b0],
        FullAxisUp_completion_sibling_separation_encodeBHist boundary,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        FullAxisUp_completion_sibling_separation_encodeBHist classifier,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        FullAxisUp_completion_sibling_separation_encodeBHist stability,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        FullAxisUp_completion_sibling_separation_encodeBHist ledger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        FullAxisUp_completion_sibling_separation_encodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        FullAxisUp_completion_sibling_separation_encodeBHist name]

def FullAxisUp_completion_sibling_separation_fromEventFlow : EventFlow → Option FullAxisUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | prefixThread :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | source :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | boundary :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | classifier :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | stability :: rest9 =>
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
                                                      | provenance :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | name :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (FullAxisUp.mk
                                                                          (FullAxisUp_completion_sibling_separation_decodeBHist
                                                                            prefixThread)
                                                                          (FullAxisUp_completion_sibling_separation_decodeBHist
                                                                            source)
                                                                          (FullAxisUp_completion_sibling_separation_decodeBHist
                                                                            boundary)
                                                                          (FullAxisUp_completion_sibling_separation_decodeBHist
                                                                            classifier)
                                                                          (FullAxisUp_completion_sibling_separation_decodeBHist
                                                                            stability)
                                                                          (FullAxisUp_completion_sibling_separation_decodeBHist
                                                                            ledger)
                                                                          (FullAxisUp_completion_sibling_separation_decodeBHist
                                                                            provenance)
                                                                          (FullAxisUp_completion_sibling_separation_decodeBHist
                                                                            name))
                                                                  | _ :: _ => none

private theorem FullAxisUp_completion_sibling_separation_round_trip :
    ∀ x : FullAxisUp,
      FullAxisUp_completion_sibling_separation_fromEventFlow
          (FullAxisUp_completion_sibling_separation_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk prefixThread source boundary classifier stability ledger provenance name =>
      change
        some
          (FullAxisUp.mk
            (FullAxisUp_completion_sibling_separation_decodeBHist
              (FullAxisUp_completion_sibling_separation_encodeBHist prefixThread))
            (FullAxisUp_completion_sibling_separation_decodeBHist
              (FullAxisUp_completion_sibling_separation_encodeBHist source))
            (FullAxisUp_completion_sibling_separation_decodeBHist
              (FullAxisUp_completion_sibling_separation_encodeBHist boundary))
            (FullAxisUp_completion_sibling_separation_decodeBHist
              (FullAxisUp_completion_sibling_separation_encodeBHist classifier))
            (FullAxisUp_completion_sibling_separation_decodeBHist
              (FullAxisUp_completion_sibling_separation_encodeBHist stability))
            (FullAxisUp_completion_sibling_separation_decodeBHist
              (FullAxisUp_completion_sibling_separation_encodeBHist ledger))
            (FullAxisUp_completion_sibling_separation_decodeBHist
              (FullAxisUp_completion_sibling_separation_encodeBHist provenance))
            (FullAxisUp_completion_sibling_separation_decodeBHist
              (FullAxisUp_completion_sibling_separation_encodeBHist name))) =
          some
            (FullAxisUp.mk prefixThread source boundary classifier stability ledger
              provenance name)
      rw [FullAxisUp_completion_sibling_separation_decode_encode_bhist prefixThread,
        FullAxisUp_completion_sibling_separation_decode_encode_bhist source,
        FullAxisUp_completion_sibling_separation_decode_encode_bhist boundary,
        FullAxisUp_completion_sibling_separation_decode_encode_bhist classifier,
        FullAxisUp_completion_sibling_separation_decode_encode_bhist stability,
        FullAxisUp_completion_sibling_separation_decode_encode_bhist ledger,
        FullAxisUp_completion_sibling_separation_decode_encode_bhist provenance,
        FullAxisUp_completion_sibling_separation_decode_encode_bhist name]

private theorem FullAxisUp_completion_sibling_separation_toEventFlow_injective
    {x y : FullAxisUp} :
    FullAxisUp_completion_sibling_separation_toEventFlow x =
      FullAxisUp_completion_sibling_separation_toEventFlow y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      FullAxisUp_completion_sibling_separation_fromEventFlow
          (FullAxisUp_completion_sibling_separation_toEventFlow x) =
        FullAxisUp_completion_sibling_separation_fromEventFlow
          (FullAxisUp_completion_sibling_separation_toEventFlow y) :=
    congrArg FullAxisUp_completion_sibling_separation_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (FullAxisUp_completion_sibling_separation_round_trip x).symm
      (Eq.trans hread (FullAxisUp_completion_sibling_separation_round_trip y)))

instance fullAxisUpBHistCarrier : BHistCarrier FullAxisUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := FullAxisUp_completion_sibling_separation_toEventFlow
  fromEventFlow := FullAxisUp_completion_sibling_separation_fromEventFlow

instance fullAxisUpChapterTasteGate : ChapterTasteGate FullAxisUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      FullAxisUp_completion_sibling_separation_fromEventFlow
          (FullAxisUp_completion_sibling_separation_toEventFlow x) =
        some x
    exact FullAxisUp_completion_sibling_separation_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FullAxisUp_completion_sibling_separation_toEventFlow_injective heq)

instance fullAxisUpFieldFaithful : FieldFaithful FullAxisUp where
  fields := fun x =>
    match x with
    | FullAxisUp.mk prefixThread source boundary classifier stability ledger provenance name =>
        [prefixThread, source, boundary, classifier, stability, ledger, provenance, name]
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | mk prefixThread₁ source₁ boundary₁ classifier₁ stability₁ ledger₁ provenance₁ name₁ =>
        cases y with
        | mk prefixThread₂ source₂ boundary₂ classifier₂ stability₂ ledger₂ provenance₂
            name₂ =>
            injection h with hPrefix t1
            injection t1 with hSource t2
            injection t2 with hBoundary t3
            injection t3 with hClassifier t4
            injection t4 with hStability t5
            injection t5 with hLedger t6
            injection t6 with hProvenance t7
            injection t7 with hName _
            subst hPrefix
            subst hSource
            subst hBoundary
            subst hClassifier
            subst hStability
            subst hLedger
            subst hProvenance
            subst hName
            rfl

theorem FullAxisUp_completion_sibling_separation (x : FullAxisUp) :
    (exists e : EventFlow, BHistCarrier.fromEventFlow e = some x) /\
      forall (w : RawEvent) (m : DisplayAlphabet),
        List.Mem w (BHistCarrier.toEventFlow x) ->
          List.Mem m w -> m = BMark.b0 \/ m = BMark.b1 := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    And.intro
      (ChapterTasteGate.no_hidden_input x)
      (ChapterTasteGate.conservativity x)

end BEDC.Derived.FullAxisUp
