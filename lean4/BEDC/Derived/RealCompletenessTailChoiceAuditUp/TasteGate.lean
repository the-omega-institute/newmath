import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealCompletenessTailChoiceAuditUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealCompletenessTailChoiceAuditUp : Type where
  | mk
      (modulus observationBudget canonicalIndex tailWindow realSeal refusal transport route
        provenance name : BHist) :
      RealCompletenessTailChoiceAuditUp
  deriving DecidableEq

def realCompletenessTailChoiceAuditEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realCompletenessTailChoiceAuditEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realCompletenessTailChoiceAuditEncodeBHist h

def realCompletenessTailChoiceAuditDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realCompletenessTailChoiceAuditDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realCompletenessTailChoiceAuditDecodeBHist tail)

private theorem realCompletenessTailChoiceAudit_decode_encode_bhist :
    ∀ h : BHist,
      realCompletenessTailChoiceAuditDecodeBHist
        (realCompletenessTailChoiceAuditEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def realCompletenessTailChoiceAuditToEventFlow :
    RealCompletenessTailChoiceAuditUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealCompletenessTailChoiceAuditUp.mk modulus observationBudget canonicalIndex tailWindow
      realSeal refusal transport route provenance name =>
      [[BMark.b0],
        realCompletenessTailChoiceAuditEncodeBHist modulus,
        [BMark.b1, BMark.b0],
        realCompletenessTailChoiceAuditEncodeBHist observationBudget,
        [BMark.b1, BMark.b1, BMark.b0],
        realCompletenessTailChoiceAuditEncodeBHist canonicalIndex,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realCompletenessTailChoiceAuditEncodeBHist tailWindow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realCompletenessTailChoiceAuditEncodeBHist realSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realCompletenessTailChoiceAuditEncodeBHist refusal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realCompletenessTailChoiceAuditEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        realCompletenessTailChoiceAuditEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        realCompletenessTailChoiceAuditEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        realCompletenessTailChoiceAuditEncodeBHist name]

def realCompletenessTailChoiceAuditFromEventFlow :
    EventFlow → Option RealCompletenessTailChoiceAuditUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | modulus :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | observationBudget :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | canonicalIndex :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | tailWindow :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | realSeal :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | refusal :: rest11 =>
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
                                                                              | name :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      some
                                                                                        (RealCompletenessTailChoiceAuditUp.mk
                                                                                          (realCompletenessTailChoiceAuditDecodeBHist
                                                                                            modulus)
                                                                                          (realCompletenessTailChoiceAuditDecodeBHist
                                                                                            observationBudget)
                                                                                          (realCompletenessTailChoiceAuditDecodeBHist
                                                                                            canonicalIndex)
                                                                                          (realCompletenessTailChoiceAuditDecodeBHist
                                                                                            tailWindow)
                                                                                          (realCompletenessTailChoiceAuditDecodeBHist
                                                                                            realSeal)
                                                                                          (realCompletenessTailChoiceAuditDecodeBHist
                                                                                            refusal)
                                                                                          (realCompletenessTailChoiceAuditDecodeBHist
                                                                                            transport)
                                                                                          (realCompletenessTailChoiceAuditDecodeBHist
                                                                                            route)
                                                                                          (realCompletenessTailChoiceAuditDecodeBHist
                                                                                            provenance)
                                                                                          (realCompletenessTailChoiceAuditDecodeBHist
                                                                                            name))
                                                                                  | _ :: _ => none

private theorem realCompletenessTailChoiceAudit_round_trip :
    ∀ x : RealCompletenessTailChoiceAuditUp,
      realCompletenessTailChoiceAuditFromEventFlow
        (realCompletenessTailChoiceAuditToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk modulus observationBudget canonicalIndex tailWindow realSeal refusal transport route
      provenance name =>
      change
        some
          (RealCompletenessTailChoiceAuditUp.mk
            (realCompletenessTailChoiceAuditDecodeBHist
              (realCompletenessTailChoiceAuditEncodeBHist modulus))
            (realCompletenessTailChoiceAuditDecodeBHist
              (realCompletenessTailChoiceAuditEncodeBHist observationBudget))
            (realCompletenessTailChoiceAuditDecodeBHist
              (realCompletenessTailChoiceAuditEncodeBHist canonicalIndex))
            (realCompletenessTailChoiceAuditDecodeBHist
              (realCompletenessTailChoiceAuditEncodeBHist tailWindow))
            (realCompletenessTailChoiceAuditDecodeBHist
              (realCompletenessTailChoiceAuditEncodeBHist realSeal))
            (realCompletenessTailChoiceAuditDecodeBHist
              (realCompletenessTailChoiceAuditEncodeBHist refusal))
            (realCompletenessTailChoiceAuditDecodeBHist
              (realCompletenessTailChoiceAuditEncodeBHist transport))
            (realCompletenessTailChoiceAuditDecodeBHist
              (realCompletenessTailChoiceAuditEncodeBHist route))
            (realCompletenessTailChoiceAuditDecodeBHist
              (realCompletenessTailChoiceAuditEncodeBHist provenance))
            (realCompletenessTailChoiceAuditDecodeBHist
              (realCompletenessTailChoiceAuditEncodeBHist name))) =
          some
            (RealCompletenessTailChoiceAuditUp.mk modulus observationBudget canonicalIndex
              tailWindow realSeal refusal transport route provenance name)
      rw [realCompletenessTailChoiceAudit_decode_encode_bhist modulus,
        realCompletenessTailChoiceAudit_decode_encode_bhist observationBudget,
        realCompletenessTailChoiceAudit_decode_encode_bhist canonicalIndex,
        realCompletenessTailChoiceAudit_decode_encode_bhist tailWindow,
        realCompletenessTailChoiceAudit_decode_encode_bhist realSeal,
        realCompletenessTailChoiceAudit_decode_encode_bhist refusal,
        realCompletenessTailChoiceAudit_decode_encode_bhist transport,
        realCompletenessTailChoiceAudit_decode_encode_bhist route,
        realCompletenessTailChoiceAudit_decode_encode_bhist provenance,
        realCompletenessTailChoiceAudit_decode_encode_bhist name]

private theorem realCompletenessTailChoiceAuditToEventFlow_injective
    {x y : RealCompletenessTailChoiceAuditUp} :
    realCompletenessTailChoiceAuditToEventFlow x =
      realCompletenessTailChoiceAuditToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realCompletenessTailChoiceAuditFromEventFlow
          (realCompletenessTailChoiceAuditToEventFlow x) =
        realCompletenessTailChoiceAuditFromEventFlow
          (realCompletenessTailChoiceAuditToEventFlow y) :=
    congrArg realCompletenessTailChoiceAuditFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realCompletenessTailChoiceAudit_round_trip x).symm
      (Eq.trans hread (realCompletenessTailChoiceAudit_round_trip y)))

instance realCompletenessTailChoiceAuditBHistCarrier :
    BHistCarrier RealCompletenessTailChoiceAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realCompletenessTailChoiceAuditToEventFlow
  fromEventFlow := realCompletenessTailChoiceAuditFromEventFlow

instance realCompletenessTailChoiceAuditChapterTasteGate :
    ChapterTasteGate RealCompletenessTailChoiceAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      realCompletenessTailChoiceAuditFromEventFlow
        (realCompletenessTailChoiceAuditToEventFlow x) = some x
    exact realCompletenessTailChoiceAudit_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realCompletenessTailChoiceAuditToEventFlow_injective heq)

instance realCompletenessTailChoiceAuditFieldFaithful :
    FieldFaithful RealCompletenessTailChoiceAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | RealCompletenessTailChoiceAuditUp.mk modulus observationBudget canonicalIndex
        tailWindow realSeal refusal transport route provenance name =>
        [modulus, observationBudget, canonicalIndex, tailWindow, realSeal, refusal, transport,
          route, provenance, name]
  field_faithful := by
    intro x y h
    cases x with
    | mk modulus₁ observationBudget₁ canonicalIndex₁ tailWindow₁ realSeal₁ refusal₁
        transport₁ route₁ provenance₁ name₁ =>
        cases y with
        | mk modulus₂ observationBudget₂ canonicalIndex₂ tailWindow₂ realSeal₂ refusal₂
            transport₂ route₂ provenance₂ name₂ =>
            simp only [] at h
            cases h
            rfl

instance realCompletenessTailChoiceAuditNontrivial :
    Nontrivial RealCompletenessTailChoiceAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealCompletenessTailChoiceAuditUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealCompletenessTailChoiceAuditUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealCompletenessTailChoiceAuditUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realCompletenessTailChoiceAuditChapterTasteGate

theorem RealCompletenessTailChoiceAuditTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      realCompletenessTailChoiceAuditDecodeBHist
        (realCompletenessTailChoiceAuditEncodeBHist h) = h) ∧
      (∀ x : RealCompletenessTailChoiceAuditUp,
        realCompletenessTailChoiceAuditFromEventFlow
          (realCompletenessTailChoiceAuditToEventFlow x) = some x) ∧
        (∀ x y : RealCompletenessTailChoiceAuditUp,
          realCompletenessTailChoiceAuditToEventFlow x =
            realCompletenessTailChoiceAuditToEventFlow y → x = y) ∧
          Nonempty (ChapterTasteGate RealCompletenessTailChoiceAuditUp) ∧
            realCompletenessTailChoiceAuditEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact realCompletenessTailChoiceAudit_decode_encode_bhist
  · constructor
    · exact realCompletenessTailChoiceAudit_round_trip
    · constructor
      · intro x y heq
        exact realCompletenessTailChoiceAuditToEventFlow_injective heq
      · constructor
        · exact Nonempty.intro realCompletenessTailChoiceAuditChapterTasteGate
        · rfl

end BEDC.Derived.RealCompletenessTailChoiceAuditUp
