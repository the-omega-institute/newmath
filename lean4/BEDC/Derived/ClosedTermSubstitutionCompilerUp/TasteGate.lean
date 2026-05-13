import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

/-!
# ClosedTermSubstitutionCompilerUp TasteGate carrier.
-/

namespace BEDC.Derived.ClosedTermSubstitutionCompilerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

/-- Finite closed-term substitution compiler packet with the eight displayed BEDC rows. -/
inductive ClosedTermSubstitutionCompilerUp : Type where
  | mk :
      (termGenerator closedBoundary operation fixedWitness transport continuation provenance
        nameCert : BHist) →
      ClosedTermSubstitutionCompilerUp
  deriving DecidableEq

def closedTermSubstitutionCompilerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: closedTermSubstitutionCompilerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: closedTermSubstitutionCompilerEncodeBHist h

def closedTermSubstitutionCompilerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (closedTermSubstitutionCompilerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (closedTermSubstitutionCompilerDecodeBHist tail)

private theorem closedTermSubstitutionCompilerDecodeEncodeBHist :
    ∀ h : BHist,
      closedTermSubstitutionCompilerDecodeBHist
          (closedTermSubstitutionCompilerEncodeBHist h) =
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

def closedTermSubstitutionCompilerToEventFlow :
    ClosedTermSubstitutionCompilerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ClosedTermSubstitutionCompilerUp.mk termGenerator closedBoundary operation fixedWitness
      transport continuation provenance nameCert =>
      [[BMark.b0],
        closedTermSubstitutionCompilerEncodeBHist termGenerator,
        [BMark.b1, BMark.b0],
        closedTermSubstitutionCompilerEncodeBHist closedBoundary,
        [BMark.b1, BMark.b1, BMark.b0],
        closedTermSubstitutionCompilerEncodeBHist operation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closedTermSubstitutionCompilerEncodeBHist fixedWitness,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closedTermSubstitutionCompilerEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closedTermSubstitutionCompilerEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closedTermSubstitutionCompilerEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        closedTermSubstitutionCompilerEncodeBHist nameCert]

def closedTermSubstitutionCompilerFromEventFlow :
    EventFlow → Option ClosedTermSubstitutionCompilerUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | termGenerator :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | closedBoundary :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | operation :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | fixedWitness :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | transport :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | continuation :: rest11 =>
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
                                                              | nameCert :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (ClosedTermSubstitutionCompilerUp.mk
                                                                          (closedTermSubstitutionCompilerDecodeBHist
                                                                            termGenerator)
                                                                          (closedTermSubstitutionCompilerDecodeBHist
                                                                            closedBoundary)
                                                                          (closedTermSubstitutionCompilerDecodeBHist
                                                                            operation)
                                                                          (closedTermSubstitutionCompilerDecodeBHist
                                                                            fixedWitness)
                                                                          (closedTermSubstitutionCompilerDecodeBHist
                                                                            transport)
                                                                          (closedTermSubstitutionCompilerDecodeBHist
                                                                            continuation)
                                                                          (closedTermSubstitutionCompilerDecodeBHist
                                                                            provenance)
                                                                          (closedTermSubstitutionCompilerDecodeBHist
                                                                            nameCert))
                                                                  | _ :: _ => none

private theorem closedTermSubstitutionCompilerRoundTrip :
    ∀ x : ClosedTermSubstitutionCompilerUp,
      closedTermSubstitutionCompilerFromEventFlow
          (closedTermSubstitutionCompilerToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk termGenerator closedBoundary operation fixedWitness transport continuation provenance
      nameCert =>
      change
        some
          (ClosedTermSubstitutionCompilerUp.mk
            (closedTermSubstitutionCompilerDecodeBHist
              (closedTermSubstitutionCompilerEncodeBHist termGenerator))
            (closedTermSubstitutionCompilerDecodeBHist
              (closedTermSubstitutionCompilerEncodeBHist closedBoundary))
            (closedTermSubstitutionCompilerDecodeBHist
              (closedTermSubstitutionCompilerEncodeBHist operation))
            (closedTermSubstitutionCompilerDecodeBHist
              (closedTermSubstitutionCompilerEncodeBHist fixedWitness))
            (closedTermSubstitutionCompilerDecodeBHist
              (closedTermSubstitutionCompilerEncodeBHist transport))
            (closedTermSubstitutionCompilerDecodeBHist
              (closedTermSubstitutionCompilerEncodeBHist continuation))
            (closedTermSubstitutionCompilerDecodeBHist
              (closedTermSubstitutionCompilerEncodeBHist provenance))
            (closedTermSubstitutionCompilerDecodeBHist
              (closedTermSubstitutionCompilerEncodeBHist nameCert))) =
          some
            (ClosedTermSubstitutionCompilerUp.mk termGenerator closedBoundary operation
              fixedWitness transport continuation provenance nameCert)
      rw [closedTermSubstitutionCompilerDecodeEncodeBHist termGenerator,
        closedTermSubstitutionCompilerDecodeEncodeBHist closedBoundary,
        closedTermSubstitutionCompilerDecodeEncodeBHist operation,
        closedTermSubstitutionCompilerDecodeEncodeBHist fixedWitness,
        closedTermSubstitutionCompilerDecodeEncodeBHist transport,
        closedTermSubstitutionCompilerDecodeEncodeBHist continuation,
        closedTermSubstitutionCompilerDecodeEncodeBHist provenance,
        closedTermSubstitutionCompilerDecodeEncodeBHist nameCert]

private theorem closedTermSubstitutionCompilerToEventFlow_injective
    {x y : ClosedTermSubstitutionCompilerUp} :
    closedTermSubstitutionCompilerToEventFlow x =
        closedTermSubstitutionCompilerToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      closedTermSubstitutionCompilerFromEventFlow
          (closedTermSubstitutionCompilerToEventFlow x) =
        closedTermSubstitutionCompilerFromEventFlow
          (closedTermSubstitutionCompilerToEventFlow y) :=
    congrArg closedTermSubstitutionCompilerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (closedTermSubstitutionCompilerRoundTrip x).symm
      (Eq.trans hread (closedTermSubstitutionCompilerRoundTrip y)))

instance closedTermSubstitutionCompilerBHistCarrier :
    BHistCarrier ClosedTermSubstitutionCompilerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := closedTermSubstitutionCompilerToEventFlow
  fromEventFlow := closedTermSubstitutionCompilerFromEventFlow

instance closedTermSubstitutionCompilerChapterTasteGate :
    ChapterTasteGate ClosedTermSubstitutionCompilerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      closedTermSubstitutionCompilerFromEventFlow
          (closedTermSubstitutionCompilerToEventFlow x) =
        some x
    exact closedTermSubstitutionCompilerRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (closedTermSubstitutionCompilerToEventFlow_injective heq)

def taste_gate : ChapterTasteGate ClosedTermSubstitutionCompilerUp :=
  closedTermSubstitutionCompilerChapterTasteGate

theorem ClosedTermSubstitutionCompilerTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      closedTermSubstitutionCompilerDecodeBHist
          (closedTermSubstitutionCompilerEncodeBHist h) =
        h) ∧
      (∀ x : ClosedTermSubstitutionCompilerUp,
        closedTermSubstitutionCompilerFromEventFlow
            (closedTermSubstitutionCompilerToEventFlow x) =
          some x) ∧
        (∀ x y : ClosedTermSubstitutionCompilerUp,
          closedTermSubstitutionCompilerToEventFlow x =
              closedTermSubstitutionCompilerToEventFlow y →
            x = y) ∧
          closedTermSubstitutionCompilerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact closedTermSubstitutionCompilerDecodeEncodeBHist
  · constructor
    · exact closedTermSubstitutionCompilerRoundTrip
    · constructor
      · intro x y heq
        exact closedTermSubstitutionCompilerToEventFlow_injective heq
      · rfl

end BEDC.Derived.ClosedTermSubstitutionCompilerUp
