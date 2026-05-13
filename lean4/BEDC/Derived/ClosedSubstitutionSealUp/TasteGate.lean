import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ClosedSubstitutionSealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ClosedSubstitutionSealUp : Type where
  | mk :
      (term depth payload closedness substitution shift audit handoff transport continuation
        provenance name : BHist) ->
        ClosedSubstitutionSealUp
  deriving DecidableEq

def closedSubstitutionSealEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: closedSubstitutionSealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: closedSubstitutionSealEncodeBHist h

def closedSubstitutionSealDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (closedSubstitutionSealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (closedSubstitutionSealDecodeBHist tail)

private theorem closedSubstitutionSealDecode_encode_bhist :
    forall h : BHist,
      closedSubstitutionSealDecodeBHist (closedSubstitutionSealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def closedSubstitutionSealToEventFlow : ClosedSubstitutionSealUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ClosedSubstitutionSealUp.mk term depth payload closedness substitution shift audit handoff
      transport continuation provenance name =>
      [[BMark.b0],
        closedSubstitutionSealEncodeBHist term,
        [BMark.b1, BMark.b0],
        closedSubstitutionSealEncodeBHist depth,
        [BMark.b1, BMark.b1, BMark.b0],
        closedSubstitutionSealEncodeBHist payload,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closedSubstitutionSealEncodeBHist closedness,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closedSubstitutionSealEncodeBHist substitution,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closedSubstitutionSealEncodeBHist shift,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closedSubstitutionSealEncodeBHist audit,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        closedSubstitutionSealEncodeBHist handoff,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        closedSubstitutionSealEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        closedSubstitutionSealEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closedSubstitutionSealEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closedSubstitutionSealEncodeBHist name]

def closedSubstitutionSealFromEventFlow : EventFlow -> Option ClosedSubstitutionSealUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | term :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | depth :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | payload :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | closedness :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | substitution :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | shift :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | audit :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | handoff :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | transport :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | continuation :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | provenance :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] => none
                                                                                          | _tag11 :: rest22 =>
                                                                                              match rest22 with
                                                                                              | [] => none
                                                                                              | name :: rest23 =>
                                                                                                  match rest23 with
                                                                                                  | [] =>
                                                                                                      some
                                                                                                        (ClosedSubstitutionSealUp.mk
                                                                                                          (closedSubstitutionSealDecodeBHist
                                                                                                            term)
                                                                                                          (closedSubstitutionSealDecodeBHist
                                                                                                            depth)
                                                                                                          (closedSubstitutionSealDecodeBHist
                                                                                                            payload)
                                                                                                          (closedSubstitutionSealDecodeBHist
                                                                                                            closedness)
                                                                                                          (closedSubstitutionSealDecodeBHist
                                                                                                            substitution)
                                                                                                          (closedSubstitutionSealDecodeBHist
                                                                                                            shift)
                                                                                                          (closedSubstitutionSealDecodeBHist
                                                                                                            audit)
                                                                                                          (closedSubstitutionSealDecodeBHist
                                                                                                            handoff)
                                                                                                          (closedSubstitutionSealDecodeBHist
                                                                                                            transport)
                                                                                                          (closedSubstitutionSealDecodeBHist
                                                                                                            continuation)
                                                                                                          (closedSubstitutionSealDecodeBHist
                                                                                                            provenance)
                                                                                                          (closedSubstitutionSealDecodeBHist
                                                                                                            name))
                                                                                                  | _ :: _ => none

private theorem closedSubstitutionSeal_round_trip :
    forall x : ClosedSubstitutionSealUp,
      closedSubstitutionSealFromEventFlow (closedSubstitutionSealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk term depth payload closedness substitution shift audit handoff transport continuation
      provenance name =>
      change
        some
          (ClosedSubstitutionSealUp.mk
            (closedSubstitutionSealDecodeBHist (closedSubstitutionSealEncodeBHist term))
            (closedSubstitutionSealDecodeBHist (closedSubstitutionSealEncodeBHist depth))
            (closedSubstitutionSealDecodeBHist (closedSubstitutionSealEncodeBHist payload))
            (closedSubstitutionSealDecodeBHist (closedSubstitutionSealEncodeBHist closedness))
            (closedSubstitutionSealDecodeBHist
              (closedSubstitutionSealEncodeBHist substitution))
            (closedSubstitutionSealDecodeBHist (closedSubstitutionSealEncodeBHist shift))
            (closedSubstitutionSealDecodeBHist (closedSubstitutionSealEncodeBHist audit))
            (closedSubstitutionSealDecodeBHist (closedSubstitutionSealEncodeBHist handoff))
            (closedSubstitutionSealDecodeBHist
              (closedSubstitutionSealEncodeBHist transport))
            (closedSubstitutionSealDecodeBHist
              (closedSubstitutionSealEncodeBHist continuation))
            (closedSubstitutionSealDecodeBHist
              (closedSubstitutionSealEncodeBHist provenance))
            (closedSubstitutionSealDecodeBHist (closedSubstitutionSealEncodeBHist name))) =
          some
            (ClosedSubstitutionSealUp.mk term depth payload closedness substitution shift audit
              handoff transport continuation provenance name)
      rw [closedSubstitutionSealDecode_encode_bhist term,
        closedSubstitutionSealDecode_encode_bhist depth,
        closedSubstitutionSealDecode_encode_bhist payload,
        closedSubstitutionSealDecode_encode_bhist closedness,
        closedSubstitutionSealDecode_encode_bhist substitution,
        closedSubstitutionSealDecode_encode_bhist shift,
        closedSubstitutionSealDecode_encode_bhist audit,
        closedSubstitutionSealDecode_encode_bhist handoff,
        closedSubstitutionSealDecode_encode_bhist transport,
        closedSubstitutionSealDecode_encode_bhist continuation,
        closedSubstitutionSealDecode_encode_bhist provenance,
        closedSubstitutionSealDecode_encode_bhist name]

private theorem closedSubstitutionSealToEventFlow_injective {x y : ClosedSubstitutionSealUp} :
    closedSubstitutionSealToEventFlow x = closedSubstitutionSealToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      closedSubstitutionSealFromEventFlow (closedSubstitutionSealToEventFlow x) =
        closedSubstitutionSealFromEventFlow (closedSubstitutionSealToEventFlow y) :=
    congrArg closedSubstitutionSealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (closedSubstitutionSeal_round_trip x).symm
      (Eq.trans hread (closedSubstitutionSeal_round_trip y)))

instance closedSubstitutionSealBHistCarrier : BHistCarrier ClosedSubstitutionSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := closedSubstitutionSealToEventFlow
  fromEventFlow := closedSubstitutionSealFromEventFlow

instance closedSubstitutionSealChapterTasteGate : ChapterTasteGate ClosedSubstitutionSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change closedSubstitutionSealFromEventFlow (closedSubstitutionSealToEventFlow x) = some x
    exact closedSubstitutionSeal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (closedSubstitutionSealToEventFlow_injective heq)

theorem ClosedSubstitutionSealTasteGate_single_carrier_alignment :
    (forall h : BHist, closedSubstitutionSealDecodeBHist
      (closedSubstitutionSealEncodeBHist h) = h) /\
      (forall x : ClosedSubstitutionSealUp,
        closedSubstitutionSealFromEventFlow (closedSubstitutionSealToEventFlow x) = some x) /\
        (forall x y : ClosedSubstitutionSealUp,
          closedSubstitutionSealToEventFlow x = closedSubstitutionSealToEventFlow y -> x = y) /\
          closedSubstitutionSealEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  have hdecode :
      forall h : BHist,
        closedSubstitutionSealDecodeBHist (closedSubstitutionSealEncodeBHist h) = h := by
    intro h
    induction h with
    | Empty =>
        rfl
    | e0 h ih =>
        exact congrArg BHist.e0 ih
    | e1 h ih =>
        exact congrArg BHist.e1 ih
  have hround :
      forall x : ClosedSubstitutionSealUp,
        closedSubstitutionSealFromEventFlow (closedSubstitutionSealToEventFlow x) = some x := by
    intro x
    cases x with
    | mk term depth payload closedness substitution shift audit handoff transport continuation
        provenance name =>
        change
          some
            (ClosedSubstitutionSealUp.mk
              (closedSubstitutionSealDecodeBHist (closedSubstitutionSealEncodeBHist term))
              (closedSubstitutionSealDecodeBHist (closedSubstitutionSealEncodeBHist depth))
              (closedSubstitutionSealDecodeBHist (closedSubstitutionSealEncodeBHist payload))
              (closedSubstitutionSealDecodeBHist
                (closedSubstitutionSealEncodeBHist closedness))
              (closedSubstitutionSealDecodeBHist
                (closedSubstitutionSealEncodeBHist substitution))
              (closedSubstitutionSealDecodeBHist (closedSubstitutionSealEncodeBHist shift))
              (closedSubstitutionSealDecodeBHist (closedSubstitutionSealEncodeBHist audit))
              (closedSubstitutionSealDecodeBHist (closedSubstitutionSealEncodeBHist handoff))
              (closedSubstitutionSealDecodeBHist
                (closedSubstitutionSealEncodeBHist transport))
              (closedSubstitutionSealDecodeBHist
                (closedSubstitutionSealEncodeBHist continuation))
              (closedSubstitutionSealDecodeBHist
                (closedSubstitutionSealEncodeBHist provenance))
              (closedSubstitutionSealDecodeBHist (closedSubstitutionSealEncodeBHist name))) =
            some
              (ClosedSubstitutionSealUp.mk term depth payload closedness substitution shift audit
                handoff transport continuation provenance name)
        rw [hdecode term, hdecode depth, hdecode payload, hdecode closedness,
          hdecode substitution, hdecode shift, hdecode audit, hdecode handoff,
          hdecode transport, hdecode continuation, hdecode provenance, hdecode name]
  have hinj :
      forall x y : ClosedSubstitutionSealUp,
        closedSubstitutionSealToEventFlow x = closedSubstitutionSealToEventFlow y -> x = y := by
    intro x y heq
    have hread :
        closedSubstitutionSealFromEventFlow (closedSubstitutionSealToEventFlow x) =
          closedSubstitutionSealFromEventFlow (closedSubstitutionSealToEventFlow y) :=
      congrArg closedSubstitutionSealFromEventFlow heq
    exact Option.some.inj (Eq.trans (hround x).symm (Eq.trans hread (hround y)))
  exact And.intro hdecode (And.intro hround (And.intro hinj rfl))

end BEDC.Derived.ClosedSubstitutionSealUp
