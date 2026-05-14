import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealSealCongruenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

/-- Real seal congruence packet with the twelve displayed BHist rows. -/
inductive RealSealCongruenceUp : Type where
  | mk :
      (readbackLeft windowLeft sealLeft readbackRight windowRight sealRight sharedClassifier
        congruence transports routes provenance nameCert : BHist) →
      RealSealCongruenceUp
  deriving DecidableEq

def realSealCongruenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realSealCongruenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realSealCongruenceEncodeBHist h

def realSealCongruenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realSealCongruenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realSealCongruenceDecodeBHist tail)

private theorem realSealCongruence_decode_encode_bhist :
    ∀ h : BHist, realSealCongruenceDecodeBHist (realSealCongruenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def realSealCongruenceFields : RealSealCongruenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealSealCongruenceUp.mk readbackLeft windowLeft sealLeft readbackRight windowRight
      sealRight sharedClassifier congruence transports routes provenance nameCert =>
      [readbackLeft, windowLeft, sealLeft, readbackRight, windowRight, sealRight,
        sharedClassifier, congruence, transports, routes, provenance, nameCert]

def realSealCongruenceToEventFlow : RealSealCongruenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (realSealCongruenceFields x).map realSealCongruenceEncodeBHist

def realSealCongruenceFromEventFlow : EventFlow → Option RealSealCongruenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | readbackLeft :: rest0 =>
      match rest0 with
      | [] => none
      | windowLeft :: rest1 =>
          match rest1 with
          | [] => none
          | sealLeft :: rest2 =>
              match rest2 with
              | [] => none
              | readbackRight :: rest3 =>
                  match rest3 with
                  | [] => none
                  | windowRight :: rest4 =>
                      match rest4 with
                      | [] => none
                      | sealRight :: rest5 =>
                          match rest5 with
                          | [] => none
                          | sharedClassifier :: rest6 =>
                              match rest6 with
                              | [] => none
                              | congruence :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | transports :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | routes :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | provenance :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | nameCert :: rest11 =>
                                                  match rest11 with
                                                  | [] =>
                                                      some
                                                        (RealSealCongruenceUp.mk
                                                          (realSealCongruenceDecodeBHist
                                                            readbackLeft)
                                                          (realSealCongruenceDecodeBHist
                                                            windowLeft)
                                                          (realSealCongruenceDecodeBHist
                                                            sealLeft)
                                                          (realSealCongruenceDecodeBHist
                                                            readbackRight)
                                                          (realSealCongruenceDecodeBHist
                                                            windowRight)
                                                          (realSealCongruenceDecodeBHist
                                                            sealRight)
                                                          (realSealCongruenceDecodeBHist
                                                            sharedClassifier)
                                                          (realSealCongruenceDecodeBHist
                                                            congruence)
                                                          (realSealCongruenceDecodeBHist
                                                            transports)
                                                          (realSealCongruenceDecodeBHist
                                                            routes)
                                                          (realSealCongruenceDecodeBHist
                                                            provenance)
                                                          (realSealCongruenceDecodeBHist
                                                            nameCert))
                                                  | _ :: _ => none

private theorem realSealCongruence_round_trip :
    ∀ x : RealSealCongruenceUp,
      realSealCongruenceFromEventFlow (realSealCongruenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk readbackLeft windowLeft sealLeft readbackRight windowRight sealRight sharedClassifier
      congruence transports routes provenance nameCert =>
      change
        some
          (RealSealCongruenceUp.mk
            (realSealCongruenceDecodeBHist (realSealCongruenceEncodeBHist readbackLeft))
            (realSealCongruenceDecodeBHist (realSealCongruenceEncodeBHist windowLeft))
            (realSealCongruenceDecodeBHist (realSealCongruenceEncodeBHist sealLeft))
            (realSealCongruenceDecodeBHist (realSealCongruenceEncodeBHist readbackRight))
            (realSealCongruenceDecodeBHist (realSealCongruenceEncodeBHist windowRight))
            (realSealCongruenceDecodeBHist (realSealCongruenceEncodeBHist sealRight))
            (realSealCongruenceDecodeBHist
              (realSealCongruenceEncodeBHist sharedClassifier))
            (realSealCongruenceDecodeBHist (realSealCongruenceEncodeBHist congruence))
            (realSealCongruenceDecodeBHist (realSealCongruenceEncodeBHist transports))
            (realSealCongruenceDecodeBHist (realSealCongruenceEncodeBHist routes))
            (realSealCongruenceDecodeBHist (realSealCongruenceEncodeBHist provenance))
            (realSealCongruenceDecodeBHist (realSealCongruenceEncodeBHist nameCert))) =
          some
            (RealSealCongruenceUp.mk readbackLeft windowLeft sealLeft readbackRight
              windowRight sealRight sharedClassifier congruence transports routes provenance
              nameCert)
      rw [realSealCongruence_decode_encode_bhist readbackLeft,
        realSealCongruence_decode_encode_bhist windowLeft,
        realSealCongruence_decode_encode_bhist sealLeft,
        realSealCongruence_decode_encode_bhist readbackRight,
        realSealCongruence_decode_encode_bhist windowRight,
        realSealCongruence_decode_encode_bhist sealRight,
        realSealCongruence_decode_encode_bhist sharedClassifier,
        realSealCongruence_decode_encode_bhist congruence,
        realSealCongruence_decode_encode_bhist transports,
        realSealCongruence_decode_encode_bhist routes,
        realSealCongruence_decode_encode_bhist provenance,
        realSealCongruence_decode_encode_bhist nameCert]

private theorem realSealCongruenceToEventFlow_injective {x y : RealSealCongruenceUp} :
    realSealCongruenceToEventFlow x = realSealCongruenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realSealCongruenceFromEventFlow (realSealCongruenceToEventFlow x) =
        realSealCongruenceFromEventFlow (realSealCongruenceToEventFlow y) :=
    congrArg realSealCongruenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realSealCongruence_round_trip x).symm
      (Eq.trans hread (realSealCongruence_round_trip y)))

private theorem realSealCongruence_fields_faithful :
    ∀ x y : RealSealCongruenceUp, realSealCongruenceFields x = realSealCongruenceFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk readbackLeft₁ windowLeft₁ sealLeft₁ readbackRight₁ windowRight₁ sealRight₁
      sharedClassifier₁ congruence₁ transports₁ routes₁ provenance₁ nameCert₁ =>
      cases y with
      | mk readbackLeft₂ windowLeft₂ sealLeft₂ readbackRight₂ windowRight₂ sealRight₂
          sharedClassifier₂ congruence₂ transports₂ routes₂ provenance₂ nameCert₂ =>
          injection hfields with hReadbackLeft tail0
          injection tail0 with hWindowLeft tail1
          injection tail1 with hSealLeft tail2
          injection tail2 with hReadbackRight tail3
          injection tail3 with hWindowRight tail4
          injection tail4 with hSealRight tail5
          injection tail5 with hSharedClassifier tail6
          injection tail6 with hCongruence tail7
          injection tail7 with hTransports tail8
          injection tail8 with hRoutes tail9
          injection tail9 with hProvenance tail10
          injection tail10 with hNameCert _
          subst hReadbackLeft
          subst hWindowLeft
          subst hSealLeft
          subst hReadbackRight
          subst hWindowRight
          subst hSealRight
          subst hSharedClassifier
          subst hCongruence
          subst hTransports
          subst hRoutes
          subst hProvenance
          subst hNameCert
          rfl

instance realSealCongruenceBHistCarrier : BHistCarrier RealSealCongruenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realSealCongruenceToEventFlow
  fromEventFlow := realSealCongruenceFromEventFlow

instance realSealCongruenceChapterTasteGate :
    ChapterTasteGate RealSealCongruenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realSealCongruenceFromEventFlow (realSealCongruenceToEventFlow x) = some x
    exact realSealCongruence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realSealCongruenceToEventFlow_injective heq)

instance realSealCongruenceFieldFaithful : FieldFaithful RealSealCongruenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realSealCongruenceFields
  field_faithful := realSealCongruence_fields_faithful

def taste_gate : ChapterTasteGate RealSealCongruenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realSealCongruenceFromEventFlow (realSealCongruenceToEventFlow x) = some x
    exact realSealCongruence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realSealCongruenceToEventFlow_injective heq)

theorem RealSealCongruenceTasteGate_single_carrier_alignment :
    (∀ h : BHist, realSealCongruenceDecodeBHist (realSealCongruenceEncodeBHist h) = h) ∧
      (∀ x : RealSealCongruenceUp,
        realSealCongruenceFromEventFlow (realSealCongruenceToEventFlow x) = some x) ∧
        (∀ x y : RealSealCongruenceUp,
          realSealCongruenceToEventFlow x = realSealCongruenceToEventFlow y → x = y) ∧
          realSealCongruenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact realSealCongruence_decode_encode_bhist
  · constructor
    · exact realSealCongruence_round_trip
    · constructor
      · intro x y heq
        exact realSealCongruenceToEventFlow_injective heq
      · rfl

end BEDC.Derived.RealSealCongruenceUp
