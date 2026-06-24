import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

/-!
# LocatedRealCauchyCompletenessUp TasteGate carrier.
-/

namespace BEDC.Derived.LocatedRealCauchyCompletenessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

/-- Finite located-real Cauchy completeness packet with the ten displayed BEDC rows. -/
inductive LocatedRealCauchyCompletenessUp : Type where
  | mk :
      (locatedAdmission modulus window dyadic regularReadback realSeal transport replay
        provenance name : BHist) →
      LocatedRealCauchyCompletenessUp
  deriving DecidableEq

def locatedRealCauchyCompletenessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedRealCauchyCompletenessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedRealCauchyCompletenessEncodeBHist h

def locatedRealCauchyCompletenessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedRealCauchyCompletenessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedRealCauchyCompletenessDecodeBHist tail)

private theorem LocatedRealCauchyCompletenessTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      locatedRealCauchyCompletenessDecodeBHist
          (locatedRealCauchyCompletenessEncodeBHist h) =
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

def locatedRealCauchyCompletenessToEventFlow :
    LocatedRealCauchyCompletenessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedRealCauchyCompletenessUp.mk locatedAdmission modulus window dyadic
      regularReadback realSeal transport replay provenance name =>
      [[BMark.b0],
        locatedRealCauchyCompletenessEncodeBHist locatedAdmission,
        [BMark.b1, BMark.b0],
        locatedRealCauchyCompletenessEncodeBHist modulus,
        [BMark.b1, BMark.b1, BMark.b0],
        locatedRealCauchyCompletenessEncodeBHist window,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        locatedRealCauchyCompletenessEncodeBHist dyadic,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        locatedRealCauchyCompletenessEncodeBHist regularReadback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        locatedRealCauchyCompletenessEncodeBHist realSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        locatedRealCauchyCompletenessEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        locatedRealCauchyCompletenessEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        locatedRealCauchyCompletenessEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        locatedRealCauchyCompletenessEncodeBHist name]

def locatedRealCauchyCompletenessFromEventFlow :
    EventFlow → Option LocatedRealCauchyCompletenessUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | locatedAdmission :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | modulus :: rest3 =>
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
                                      | regularReadback :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | realSeal :: rest11 =>
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
                                                              | replay :: rest15 =>
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
                                                                                        (LocatedRealCauchyCompletenessUp.mk
                                                                                          (locatedRealCauchyCompletenessDecodeBHist
                                                                                            locatedAdmission)
                                                                                          (locatedRealCauchyCompletenessDecodeBHist
                                                                                            modulus)
                                                                                          (locatedRealCauchyCompletenessDecodeBHist
                                                                                            window)
                                                                                          (locatedRealCauchyCompletenessDecodeBHist
                                                                                            dyadic)
                                                                                          (locatedRealCauchyCompletenessDecodeBHist
                                                                                            regularReadback)
                                                                                          (locatedRealCauchyCompletenessDecodeBHist
                                                                                            realSeal)
                                                                                          (locatedRealCauchyCompletenessDecodeBHist
                                                                                            transport)
                                                                                          (locatedRealCauchyCompletenessDecodeBHist
                                                                                            replay)
                                                                                          (locatedRealCauchyCompletenessDecodeBHist
                                                                                            provenance)
                                                                                          (locatedRealCauchyCompletenessDecodeBHist
                                                                                            name))
                                                                                  | _ :: _ => none

private theorem LocatedRealCauchyCompletenessTasteGate_single_carrier_alignment_round :
    ∀ x : LocatedRealCauchyCompletenessUp,
      locatedRealCauchyCompletenessFromEventFlow
          (locatedRealCauchyCompletenessToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk locatedAdmission modulus window dyadic regularReadback realSeal transport replay
      provenance name =>
      change
        some
          (LocatedRealCauchyCompletenessUp.mk
            (locatedRealCauchyCompletenessDecodeBHist
              (locatedRealCauchyCompletenessEncodeBHist locatedAdmission))
            (locatedRealCauchyCompletenessDecodeBHist
              (locatedRealCauchyCompletenessEncodeBHist modulus))
            (locatedRealCauchyCompletenessDecodeBHist
              (locatedRealCauchyCompletenessEncodeBHist window))
            (locatedRealCauchyCompletenessDecodeBHist
              (locatedRealCauchyCompletenessEncodeBHist dyadic))
            (locatedRealCauchyCompletenessDecodeBHist
              (locatedRealCauchyCompletenessEncodeBHist regularReadback))
            (locatedRealCauchyCompletenessDecodeBHist
              (locatedRealCauchyCompletenessEncodeBHist realSeal))
            (locatedRealCauchyCompletenessDecodeBHist
              (locatedRealCauchyCompletenessEncodeBHist transport))
            (locatedRealCauchyCompletenessDecodeBHist
              (locatedRealCauchyCompletenessEncodeBHist replay))
            (locatedRealCauchyCompletenessDecodeBHist
              (locatedRealCauchyCompletenessEncodeBHist provenance))
            (locatedRealCauchyCompletenessDecodeBHist
              (locatedRealCauchyCompletenessEncodeBHist name))) =
          some
            (LocatedRealCauchyCompletenessUp.mk locatedAdmission modulus window dyadic
              regularReadback realSeal transport replay provenance name)
      rw [LocatedRealCauchyCompletenessTasteGate_single_carrier_alignment_decode]
      rw [LocatedRealCauchyCompletenessTasteGate_single_carrier_alignment_decode]
      rw [LocatedRealCauchyCompletenessTasteGate_single_carrier_alignment_decode]
      rw [LocatedRealCauchyCompletenessTasteGate_single_carrier_alignment_decode]
      rw [LocatedRealCauchyCompletenessTasteGate_single_carrier_alignment_decode]
      rw [LocatedRealCauchyCompletenessTasteGate_single_carrier_alignment_decode]
      rw [LocatedRealCauchyCompletenessTasteGate_single_carrier_alignment_decode]
      rw [LocatedRealCauchyCompletenessTasteGate_single_carrier_alignment_decode]
      rw [LocatedRealCauchyCompletenessTasteGate_single_carrier_alignment_decode]
      rw [LocatedRealCauchyCompletenessTasteGate_single_carrier_alignment_decode]

private theorem LocatedRealCauchyCompletenessTasteGate_single_carrier_alignment_injective
    {x y : LocatedRealCauchyCompletenessUp} :
    locatedRealCauchyCompletenessToEventFlow x =
      locatedRealCauchyCompletenessToEventFlow y →
    x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedRealCauchyCompletenessFromEventFlow
          (locatedRealCauchyCompletenessToEventFlow x) =
        locatedRealCauchyCompletenessFromEventFlow
          (locatedRealCauchyCompletenessToEventFlow y) :=
    congrArg locatedRealCauchyCompletenessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (LocatedRealCauchyCompletenessTasteGate_single_carrier_alignment_round x).symm
      (Eq.trans hread
        (LocatedRealCauchyCompletenessTasteGate_single_carrier_alignment_round y)))

instance locatedRealCauchyCompletenessBHistCarrier :
    BHistCarrier LocatedRealCauchyCompletenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedRealCauchyCompletenessToEventFlow
  fromEventFlow := locatedRealCauchyCompletenessFromEventFlow

instance locatedRealCauchyCompletenessChapterTasteGate :
    ChapterTasteGate LocatedRealCauchyCompletenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      locatedRealCauchyCompletenessFromEventFlow
          (locatedRealCauchyCompletenessToEventFlow x) =
        some x
    exact LocatedRealCauchyCompletenessTasteGate_single_carrier_alignment_round x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (LocatedRealCauchyCompletenessTasteGate_single_carrier_alignment_injective heq)

theorem LocatedRealCauchyCompletenessTasteGate_single_carrier_alignment :
    locatedRealCauchyCompletenessEncodeBHist BHist.Empty = ([] : List BMark) ∧
      (∀ h : BHist,
        locatedRealCauchyCompletenessDecodeBHist
            (locatedRealCauchyCompletenessEncodeBHist h) =
          h) ∧
        (∀ x : LocatedRealCauchyCompletenessUp,
          locatedRealCauchyCompletenessFromEventFlow
              (locatedRealCauchyCompletenessToEventFlow x) =
            some x) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · rfl
  · constructor
    · exact LocatedRealCauchyCompletenessTasteGate_single_carrier_alignment_decode
    · exact LocatedRealCauchyCompletenessTasteGate_single_carrier_alignment_round

end BEDC.Derived.LocatedRealCauchyCompletenessUp
