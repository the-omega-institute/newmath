import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FullAxisUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FullAxisUp : Type where
  | mk : (source pattern classifier stability ledger boundary sealName : BHist) → FullAxisUp
  deriving DecidableEq

def fullAxisEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: fullAxisEncodeBHist h
  | BHist.e1 h => BMark.b1 :: fullAxisEncodeBHist h

def fullAxisDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (fullAxisDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (fullAxisDecodeBHist tail)

private theorem fullAxisDecode_encode_bhist :
    ∀ h : BHist, fullAxisDecodeBHist (fullAxisEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def fullAxisToEventFlow : FullAxisUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FullAxisUp.mk source pattern classifier stability ledger boundary sealName =>
      [[BMark.b0],
        fullAxisEncodeBHist source,
        [BMark.b1, BMark.b0],
        fullAxisEncodeBHist pattern,
        [BMark.b1, BMark.b1, BMark.b0],
        fullAxisEncodeBHist classifier,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        fullAxisEncodeBHist stability,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        fullAxisEncodeBHist ledger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        fullAxisEncodeBHist boundary,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        fullAxisEncodeBHist sealName]

def fullAxisFromEventFlow : EventFlow → Option FullAxisUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | source :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | pattern :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | classifier :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | stability :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | ledger :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | boundary :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | sealName :: rest13 =>
                                                          match rest13 with
                                                          | [] =>
                                                              some
                                                                (FullAxisUp.mk
                                                                  (fullAxisDecodeBHist source)
                                                                  (fullAxisDecodeBHist pattern)
                                                                  (fullAxisDecodeBHist classifier)
                                                                  (fullAxisDecodeBHist stability)
                                                                  (fullAxisDecodeBHist ledger)
                                                                  (fullAxisDecodeBHist boundary)
                                                                  (fullAxisDecodeBHist sealName))
                                                          | _ :: _ => none

private theorem fullAxis_round_trip :
    ∀ x : FullAxisUp, fullAxisFromEventFlow (fullAxisToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source pattern classifier stability ledger boundary sealName =>
      change
        some
          (FullAxisUp.mk
            (fullAxisDecodeBHist (fullAxisEncodeBHist source))
            (fullAxisDecodeBHist (fullAxisEncodeBHist pattern))
            (fullAxisDecodeBHist (fullAxisEncodeBHist classifier))
            (fullAxisDecodeBHist (fullAxisEncodeBHist stability))
            (fullAxisDecodeBHist (fullAxisEncodeBHist ledger))
            (fullAxisDecodeBHist (fullAxisEncodeBHist boundary))
            (fullAxisDecodeBHist (fullAxisEncodeBHist sealName))) =
          some
            (FullAxisUp.mk source pattern classifier stability ledger boundary sealName)
      rw [fullAxisDecode_encode_bhist source,
        fullAxisDecode_encode_bhist pattern,
        fullAxisDecode_encode_bhist classifier,
        fullAxisDecode_encode_bhist stability,
        fullAxisDecode_encode_bhist ledger,
        fullAxisDecode_encode_bhist boundary,
        fullAxisDecode_encode_bhist sealName]

private theorem fullAxisToEventFlow_injective {x y : FullAxisUp} :
    fullAxisToEventFlow x = fullAxisToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      fullAxisFromEventFlow (fullAxisToEventFlow x) =
        fullAxisFromEventFlow (fullAxisToEventFlow y) :=
    congrArg fullAxisFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (fullAxis_round_trip x).symm
      (Eq.trans hread (fullAxis_round_trip y)))

instance fullAxisBHistCarrier : BHistCarrier FullAxisUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := fullAxisToEventFlow
  fromEventFlow := fullAxisFromEventFlow

instance fullAxisChapterTasteGate : ChapterTasteGate FullAxisUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change fullAxisFromEventFlow (fullAxisToEventFlow x) = some x
    exact fullAxis_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (fullAxisToEventFlow_injective heq)

instance fullAxisFieldFaithful : FieldFaithful FullAxisUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | FullAxisUp.mk source pattern classifier stability ledger boundary sealName =>
        [source, pattern, classifier, stability, ledger, boundary, sealName]
  field_faithful := by
    intro x y h
    cases x with
    | mk source1 pattern1 classifier1 stability1 ledger1 boundary1 sealName1 =>
        cases y with
        | mk source2 pattern2 classifier2 stability2 ledger2 boundary2 sealName2 =>
            injection h with hsource tail1
            injection tail1 with hpattern tail2
            injection tail2 with hclassifier tail3
            injection tail3 with hstability tail4
            injection tail4 with hledger tail5
            injection tail5 with hboundary tail6
            injection tail6 with hsealName _
            subst hsource
            subst hpattern
            subst hclassifier
            subst hstability
            subst hledger
            subst hboundary
            subst hsealName
            rfl

instance fullAxisNontrivial : Nontrivial FullAxisUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FullAxisUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      FullAxisUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        injection h with hsource _ _ _ _ _ _
        cases hsource⟩

theorem FullAxisTasteGate_single_carrier_alignment :
    (∀ h : BHist, fullAxisDecodeBHist (fullAxisEncodeBHist h) = h) ∧
      (∀ x : FullAxisUp, fullAxisFromEventFlow (fullAxisToEventFlow x) = some x) ∧
        (∀ x y : FullAxisUp, fullAxisToEventFlow x = fullAxisToEventFlow y → x = y) ∧
          fullAxisEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact fullAxisDecode_encode_bhist
  · constructor
    · exact fullAxis_round_trip
    · constructor
      · intro x y heq
        exact fullAxisToEventFlow_injective heq
      · rfl

end BEDC.Derived.FullAxisUp
