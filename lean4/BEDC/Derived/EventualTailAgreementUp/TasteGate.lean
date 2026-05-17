import BEDC.Meta.TasteGate

namespace BEDC.Derived.EventualTailAgreementUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EventualTailAgreementUp : Type where
  | mk : (A B M T R D S H C P N : BHist) → EventualTailAgreementUp

def eventualTailAgreementEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: eventualTailAgreementEncodeBHist h
  | BHist.e1 h => BMark.b1 :: eventualTailAgreementEncodeBHist h

def eventualTailAgreementDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (eventualTailAgreementDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (eventualTailAgreementDecodeBHist tail)

private theorem eventualTailAgreementDecode_encode_bhist :
    ∀ h : BHist,
      eventualTailAgreementDecodeBHist (eventualTailAgreementEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def eventualTailAgreementFields : EventualTailAgreementUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | EventualTailAgreementUp.mk A B M T R D S H C P N => [A, B, M, T, R, D, S, H, C, P, N]

def eventualTailAgreementToEventFlow : EventualTailAgreementUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | EventualTailAgreementUp.mk A B M T R D S H C P N =>
      [[BMark.b0],
        eventualTailAgreementEncodeBHist A,
        [BMark.b1, BMark.b0],
        eventualTailAgreementEncodeBHist B,
        [BMark.b1, BMark.b1, BMark.b0],
        eventualTailAgreementEncodeBHist M,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        eventualTailAgreementEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        eventualTailAgreementEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        eventualTailAgreementEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        eventualTailAgreementEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        eventualTailAgreementEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        eventualTailAgreementEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        eventualTailAgreementEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        eventualTailAgreementEncodeBHist N]

def eventualTailAgreementFromEventFlow : EventFlow → Option EventualTailAgreementUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tagA :: restA =>
      match restA with
      | [] => none
      | A :: restB =>
          match restB with
          | [] => none
          | _tagB :: restM =>
              match restM with
              | [] => none
              | B :: restT =>
                  match restT with
                  | [] => none
                  | _tagM :: restR =>
                      match restR with
                      | [] => none
                      | M :: restD =>
                          match restD with
                          | [] => none
                          | _tagT :: restS =>
                              match restS with
                              | [] => none
                              | T :: restH =>
                                  match restH with
                                  | [] => none
                                  | _tagR :: restC =>
                                      match restC with
                                      | [] => none
                                      | R :: restP =>
                                          match restP with
                                          | [] => none
                                          | _tagD :: restN =>
                                              match restN with
                                              | [] => none
                                              | D :: restD2 =>
                                                  match restD2 with
                                                  | [] => none
                                                  | _tagS :: restS2 =>
                                                      match restS2 with
                                                      | [] => none
                                                      | S :: restS3 =>
                                                          match restS3 with
                                                          | [] => none
                                                          | _tagH :: restH2 =>
                                                              match restH2 with
                                                              | [] => none
                                                              | H :: restH3 =>
                                                                  match restH3 with
                                                                  | [] => none
                                                                  | _tagC :: restC2 =>
                                                                      match restC2 with
                                                                      | [] => none
                                                                      | C :: restC3 =>
                                                                          match restC3 with
                                                                          | [] => none
                                                                          | _tagP :: restP2 =>
                                                                              match restP2 with
                                                                              | [] => none
                                                                              | P :: restP3 =>
                                                                                  match restP3 with
                                                                                  | [] => none
                                                                                  | _tagN :: restN2 =>
                                                                                      match restN2 with
                                                                                      | [] => none
                                                                                      | N :: restN3 =>
                                                                                          match restN3 with
                                                                                          | [] =>
                                                                                              some
                                                                                                (EventualTailAgreementUp.mk
                                                                                                  (eventualTailAgreementDecodeBHist A)
                                                                                                  (eventualTailAgreementDecodeBHist B)
                                                                                                  (eventualTailAgreementDecodeBHist M)
                                                                                                  (eventualTailAgreementDecodeBHist T)
                                                                                                  (eventualTailAgreementDecodeBHist R)
                                                                                                  (eventualTailAgreementDecodeBHist D)
                                                                                                  (eventualTailAgreementDecodeBHist S)
                                                                                                  (eventualTailAgreementDecodeBHist H)
                                                                                                  (eventualTailAgreementDecodeBHist C)
                                                                                                  (eventualTailAgreementDecodeBHist P)
                                                                                                  (eventualTailAgreementDecodeBHist N))
                                                                                          | _ :: _ => none

private theorem eventualTailAgreement_round_trip :
    ∀ x : EventualTailAgreementUp,
      eventualTailAgreementFromEventFlow (eventualTailAgreementToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A B M T R D S H C P N =>
      change
        some
          (EventualTailAgreementUp.mk
            (eventualTailAgreementDecodeBHist (eventualTailAgreementEncodeBHist A))
            (eventualTailAgreementDecodeBHist (eventualTailAgreementEncodeBHist B))
            (eventualTailAgreementDecodeBHist (eventualTailAgreementEncodeBHist M))
            (eventualTailAgreementDecodeBHist (eventualTailAgreementEncodeBHist T))
            (eventualTailAgreementDecodeBHist (eventualTailAgreementEncodeBHist R))
            (eventualTailAgreementDecodeBHist (eventualTailAgreementEncodeBHist D))
            (eventualTailAgreementDecodeBHist (eventualTailAgreementEncodeBHist S))
            (eventualTailAgreementDecodeBHist (eventualTailAgreementEncodeBHist H))
            (eventualTailAgreementDecodeBHist (eventualTailAgreementEncodeBHist C))
            (eventualTailAgreementDecodeBHist (eventualTailAgreementEncodeBHist P))
            (eventualTailAgreementDecodeBHist (eventualTailAgreementEncodeBHist N))) =
          some (EventualTailAgreementUp.mk A B M T R D S H C P N)
      rw [eventualTailAgreementDecode_encode_bhist A,
        eventualTailAgreementDecode_encode_bhist B,
        eventualTailAgreementDecode_encode_bhist M,
        eventualTailAgreementDecode_encode_bhist T,
        eventualTailAgreementDecode_encode_bhist R,
        eventualTailAgreementDecode_encode_bhist D,
        eventualTailAgreementDecode_encode_bhist S,
        eventualTailAgreementDecode_encode_bhist H,
        eventualTailAgreementDecode_encode_bhist C,
        eventualTailAgreementDecode_encode_bhist P,
        eventualTailAgreementDecode_encode_bhist N]

private theorem eventualTailAgreementToEventFlow_injective :
    ∀ x y : EventualTailAgreementUp,
      eventualTailAgreementToEventFlow x = eventualTailAgreementToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hxy
  have hread :
      eventualTailAgreementFromEventFlow (eventualTailAgreementToEventFlow x) =
        eventualTailAgreementFromEventFlow (eventualTailAgreementToEventFlow y) :=
    congrArg eventualTailAgreementFromEventFlow hxy
  exact
    Option.some.inj
      (Eq.trans (eventualTailAgreement_round_trip x).symm
        (Eq.trans hread (eventualTailAgreement_round_trip y)))

instance eventualTailAgreementBHistCarrier : BHistCarrier EventualTailAgreementUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := eventualTailAgreementToEventFlow
  fromEventFlow := eventualTailAgreementFromEventFlow

instance eventualTailAgreementChapterTasteGate :
    ChapterTasteGate EventualTailAgreementUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change eventualTailAgreementFromEventFlow (eventualTailAgreementToEventFlow x) = some x
    exact eventualTailAgreement_round_trip x
  layer_separation := by
    intro x y hxy hflow
    exact hxy (eventualTailAgreementToEventFlow_injective x y hflow)

instance eventualTailAgreementFieldFaithful :
    FieldFaithful EventualTailAgreementUp where
  fields := eventualTailAgreementFields
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | mk A₁ B₁ M₁ T₁ R₁ D₁ S₁ H₁ C₁ P₁ N₁ =>
        cases y with
        | mk A₂ B₂ M₂ T₂ R₂ D₂ S₂ H₂ C₂ P₂ N₂ =>
            injection h with hA rest1
            injection rest1 with hB rest2
            injection rest2 with hM rest3
            injection rest3 with hT rest4
            injection rest4 with hR rest5
            injection rest5 with hD rest6
            injection rest6 with hS rest7
            injection rest7 with hH rest8
            injection rest8 with hC rest9
            injection rest9 with hP rest10
            injection rest10 with hN _
            cases hA
            cases hB
            cases hM
            cases hT
            cases hR
            cases hD
            cases hS
            cases hH
            cases hC
            cases hP
            cases hN
            rfl

instance eventualTailAgreementNontrivial : Nontrivial EventualTailAgreementUp where
  witness_pair :=
    -- BEDC touchpoint anchor: BHist BMark
    ⟨EventualTailAgreementUp.mk
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      EventualTailAgreementUp.mk
        (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate EventualTailAgreementUp :=
  -- BEDC touchpoint anchor: BHist BMark
  eventualTailAgreementChapterTasteGate

theorem EventualTailAgreementTasteGate_single_carrier_alignment :
    (∀ h : BHist, eventualTailAgreementDecodeBHist (eventualTailAgreementEncodeBHist h) = h) ∧
      (∀ x : EventualTailAgreementUp,
        eventualTailAgreementFromEventFlow (eventualTailAgreementToEventFlow x) = some x) ∧
        (∀ x y : EventualTailAgreementUp,
          eventualTailAgreementToEventFlow x = eventualTailAgreementToEventFlow y → x = y) ∧
          eventualTailAgreementEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact eventualTailAgreementDecode_encode_bhist
  · constructor
    · exact eventualTailAgreement_round_trip
    · constructor
      · exact eventualTailAgreementToEventFlow_injective
      · rfl

end BEDC.Derived.EventualTailAgreementUp
