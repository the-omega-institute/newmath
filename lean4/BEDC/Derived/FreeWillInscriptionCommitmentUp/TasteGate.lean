import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FreeWillInscriptionCommitmentUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FreeWillInscriptionCommitmentUp : Type where
  | mk :
      (priorBoundary inscriptionEvent gapProvenance classifierTransport nonReduction transports
        routes package nameCert : BHist) →
      FreeWillInscriptionCommitmentUp
  deriving DecidableEq

def freeWillInscriptionCommitmentEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: freeWillInscriptionCommitmentEncodeBHist h
  | BHist.e1 h => BMark.b1 :: freeWillInscriptionCommitmentEncodeBHist h

def freeWillInscriptionCommitmentDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (freeWillInscriptionCommitmentDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (freeWillInscriptionCommitmentDecodeBHist tail)

private theorem freeWillInscriptionCommitmentDecode_encode_bhist :
    ∀ h : BHist,
      freeWillInscriptionCommitmentDecodeBHist
        (freeWillInscriptionCommitmentEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def freeWillInscriptionCommitmentToEventFlow :
    FreeWillInscriptionCommitmentUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FreeWillInscriptionCommitmentUp.mk priorBoundary inscriptionEvent gapProvenance
      classifierTransport nonReduction transports routes package nameCert =>
      [[BMark.b0],
        freeWillInscriptionCommitmentEncodeBHist priorBoundary,
        [BMark.b1, BMark.b0],
        freeWillInscriptionCommitmentEncodeBHist inscriptionEvent,
        [BMark.b1, BMark.b1, BMark.b0],
        freeWillInscriptionCommitmentEncodeBHist gapProvenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        freeWillInscriptionCommitmentEncodeBHist classifierTransport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        freeWillInscriptionCommitmentEncodeBHist nonReduction,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        freeWillInscriptionCommitmentEncodeBHist transports,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        freeWillInscriptionCommitmentEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        freeWillInscriptionCommitmentEncodeBHist package,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        freeWillInscriptionCommitmentEncodeBHist nameCert]

def freeWillInscriptionCommitmentFromEventFlow :
    EventFlow → Option FreeWillInscriptionCommitmentUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | priorBoundary :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | inscriptionEvent :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | gapProvenance :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | classifierTransport :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | nonReduction :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | transports :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | routes :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | package :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | nameCert :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (FreeWillInscriptionCommitmentUp.mk
                                                                                  (freeWillInscriptionCommitmentDecodeBHist
                                                                                    priorBoundary)
                                                                                  (freeWillInscriptionCommitmentDecodeBHist
                                                                                    inscriptionEvent)
                                                                                  (freeWillInscriptionCommitmentDecodeBHist
                                                                                    gapProvenance)
                                                                                  (freeWillInscriptionCommitmentDecodeBHist
                                                                                    classifierTransport)
                                                                                  (freeWillInscriptionCommitmentDecodeBHist
                                                                                    nonReduction)
                                                                                  (freeWillInscriptionCommitmentDecodeBHist
                                                                                    transports)
                                                                                  (freeWillInscriptionCommitmentDecodeBHist
                                                                                    routes)
                                                                                  (freeWillInscriptionCommitmentDecodeBHist
                                                                                    package)
                                                                                  (freeWillInscriptionCommitmentDecodeBHist
                                                                                    nameCert))
                                                                          | _ :: _ => none

private theorem freeWillInscriptionCommitment_round_trip :
    ∀ x : FreeWillInscriptionCommitmentUp,
      freeWillInscriptionCommitmentFromEventFlow
        (freeWillInscriptionCommitmentToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk priorBoundary inscriptionEvent gapProvenance classifierTransport nonReduction transports
      routes package nameCert =>
      change
        some
          (FreeWillInscriptionCommitmentUp.mk
            (freeWillInscriptionCommitmentDecodeBHist
              (freeWillInscriptionCommitmentEncodeBHist priorBoundary))
            (freeWillInscriptionCommitmentDecodeBHist
              (freeWillInscriptionCommitmentEncodeBHist inscriptionEvent))
            (freeWillInscriptionCommitmentDecodeBHist
              (freeWillInscriptionCommitmentEncodeBHist gapProvenance))
            (freeWillInscriptionCommitmentDecodeBHist
              (freeWillInscriptionCommitmentEncodeBHist classifierTransport))
            (freeWillInscriptionCommitmentDecodeBHist
              (freeWillInscriptionCommitmentEncodeBHist nonReduction))
            (freeWillInscriptionCommitmentDecodeBHist
              (freeWillInscriptionCommitmentEncodeBHist transports))
            (freeWillInscriptionCommitmentDecodeBHist
              (freeWillInscriptionCommitmentEncodeBHist routes))
            (freeWillInscriptionCommitmentDecodeBHist
              (freeWillInscriptionCommitmentEncodeBHist package))
            (freeWillInscriptionCommitmentDecodeBHist
              (freeWillInscriptionCommitmentEncodeBHist nameCert))) =
          some
            (FreeWillInscriptionCommitmentUp.mk priorBoundary inscriptionEvent gapProvenance
              classifierTransport nonReduction transports routes package nameCert)
      rw [freeWillInscriptionCommitmentDecode_encode_bhist priorBoundary,
        freeWillInscriptionCommitmentDecode_encode_bhist inscriptionEvent,
        freeWillInscriptionCommitmentDecode_encode_bhist gapProvenance,
        freeWillInscriptionCommitmentDecode_encode_bhist classifierTransport,
        freeWillInscriptionCommitmentDecode_encode_bhist nonReduction,
        freeWillInscriptionCommitmentDecode_encode_bhist transports,
        freeWillInscriptionCommitmentDecode_encode_bhist routes,
        freeWillInscriptionCommitmentDecode_encode_bhist package,
        freeWillInscriptionCommitmentDecode_encode_bhist nameCert]

private theorem freeWillInscriptionCommitmentToEventFlow_injective
    {x y : FreeWillInscriptionCommitmentUp} :
    freeWillInscriptionCommitmentToEventFlow x =
      freeWillInscriptionCommitmentToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      freeWillInscriptionCommitmentFromEventFlow
          (freeWillInscriptionCommitmentToEventFlow x) =
        freeWillInscriptionCommitmentFromEventFlow
          (freeWillInscriptionCommitmentToEventFlow y) :=
    congrArg freeWillInscriptionCommitmentFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (freeWillInscriptionCommitment_round_trip x).symm
      (Eq.trans hread (freeWillInscriptionCommitment_round_trip y)))

instance freeWillInscriptionCommitmentBHistCarrier :
    BHistCarrier FreeWillInscriptionCommitmentUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := freeWillInscriptionCommitmentToEventFlow
  fromEventFlow := freeWillInscriptionCommitmentFromEventFlow

instance freeWillInscriptionCommitmentChapterTasteGate :
    ChapterTasteGate FreeWillInscriptionCommitmentUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      freeWillInscriptionCommitmentFromEventFlow
        (freeWillInscriptionCommitmentToEventFlow x) = some x
    exact freeWillInscriptionCommitment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (freeWillInscriptionCommitmentToEventFlow_injective heq)

theorem FreeWillInscriptionCommitmentTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      freeWillInscriptionCommitmentDecodeBHist
        (freeWillInscriptionCommitmentEncodeBHist h) = h) ∧
      (∀ x : FreeWillInscriptionCommitmentUp,
        freeWillInscriptionCommitmentFromEventFlow
          (freeWillInscriptionCommitmentToEventFlow x) = some x) ∧
        (∀ x y : FreeWillInscriptionCommitmentUp,
          freeWillInscriptionCommitmentToEventFlow x =
            freeWillInscriptionCommitmentToEventFlow y → x = y) ∧
          freeWillInscriptionCommitmentEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact freeWillInscriptionCommitmentDecode_encode_bhist
  · constructor
    · exact freeWillInscriptionCommitment_round_trip
    · constructor
      · intro x y heq
        exact freeWillInscriptionCommitmentToEventFlow_injective heq
      · rfl

end BEDC.Derived.FreeWillInscriptionCommitmentUp
