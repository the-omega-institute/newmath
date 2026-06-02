import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedUniformLimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedUniformLimitUp : Type where
  | mk (I S M W R E G H C P N : BHist) : LocatedUniformLimitUp
  deriving DecidableEq

def locatedUniformLimitEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedUniformLimitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedUniformLimitEncodeBHist h

def locatedUniformLimitDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedUniformLimitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedUniformLimitDecodeBHist tail)

private theorem locatedUniformLimit_decode_encode :
    ∀ h : BHist, locatedUniformLimitDecodeBHist (locatedUniformLimitEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedUniformLimitToEventFlow : LocatedUniformLimitUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedUniformLimitUp.mk I S M W R E G H C P N =>
      [[BMark.b0],
        locatedUniformLimitEncodeBHist I,
        [BMark.b1, BMark.b0],
        locatedUniformLimitEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b0],
        locatedUniformLimitEncodeBHist M,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        locatedUniformLimitEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        locatedUniformLimitEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        locatedUniformLimitEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        locatedUniformLimitEncodeBHist G,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        locatedUniformLimitEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        locatedUniformLimitEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        locatedUniformLimitEncodeBHist P,
        locatedUniformLimitEncodeBHist N]

def locatedUniformLimitFromEventFlow : EventFlow → Option LocatedUniformLimitUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | I :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | S :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | M :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | W :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | R :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | E :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | G :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | H :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | C :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 ::
                                                                              rest18 =>
                                                                              match rest18 with
                                                                              | [] =>
                                                                                  none
                                                                              | P ::
                                                                                  rest19 =>
                                                                                  match rest19
                                                                                    with
                                                                                  | [] =>
                                                                                      none
                                                                                  | N ::
                                                                                      rest20 =>
                                                                                      match
                                                                                        rest20
                                                                                        with
                                                                                      | [] =>
                                                                                          some
                                                                                            (LocatedUniformLimitUp.mk
                                                                                              (locatedUniformLimitDecodeBHist I)
                                                                                              (locatedUniformLimitDecodeBHist S)
                                                                                              (locatedUniformLimitDecodeBHist M)
                                                                                              (locatedUniformLimitDecodeBHist W)
                                                                                              (locatedUniformLimitDecodeBHist R)
                                                                                              (locatedUniformLimitDecodeBHist E)
                                                                                              (locatedUniformLimitDecodeBHist G)
                                                                                              (locatedUniformLimitDecodeBHist H)
                                                                                              (locatedUniformLimitDecodeBHist C)
                                                                                              (locatedUniformLimitDecodeBHist P)
                                                                                              (locatedUniformLimitDecodeBHist N))
                                                                                      | _ :: _ =>
                                                                                          none

private theorem locatedUniformLimit_round_trip :
    ∀ x : LocatedUniformLimitUp,
      locatedUniformLimitFromEventFlow (locatedUniformLimitToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I S M W R E G H C P N =>
      let i' := locatedUniformLimitDecodeBHist (locatedUniformLimitEncodeBHist I)
      let s' := locatedUniformLimitDecodeBHist (locatedUniformLimitEncodeBHist S)
      let m' := locatedUniformLimitDecodeBHist (locatedUniformLimitEncodeBHist M)
      let w' := locatedUniformLimitDecodeBHist (locatedUniformLimitEncodeBHist W)
      let r' := locatedUniformLimitDecodeBHist (locatedUniformLimitEncodeBHist R)
      let e' := locatedUniformLimitDecodeBHist (locatedUniformLimitEncodeBHist E)
      let g' := locatedUniformLimitDecodeBHist (locatedUniformLimitEncodeBHist G)
      let h' := locatedUniformLimitDecodeBHist (locatedUniformLimitEncodeBHist H)
      let c' := locatedUniformLimitDecodeBHist (locatedUniformLimitEncodeBHist C)
      let p' := locatedUniformLimitDecodeBHist (locatedUniformLimitEncodeBHist P)
      let n' := locatedUniformLimitDecodeBHist (locatedUniformLimitEncodeBHist N)
      calc
        some (LocatedUniformLimitUp.mk i' s' m' w' r' e' g' h' c' p' n') =
            some (LocatedUniformLimitUp.mk I s' m' w' r' e' g' h' c' p' n') :=
          congrArg some
            (congrArg (fun z => LocatedUniformLimitUp.mk z s' m' w' r' e' g' h' c' p' n')
              (locatedUniformLimit_decode_encode I))
        _ = some (LocatedUniformLimitUp.mk I S m' w' r' e' g' h' c' p' n') :=
          congrArg some
            (congrArg (fun z => LocatedUniformLimitUp.mk I z m' w' r' e' g' h' c' p' n')
              (locatedUniformLimit_decode_encode S))
        _ = some (LocatedUniformLimitUp.mk I S M w' r' e' g' h' c' p' n') :=
          congrArg some
            (congrArg (fun z => LocatedUniformLimitUp.mk I S z w' r' e' g' h' c' p' n')
              (locatedUniformLimit_decode_encode M))
        _ = some (LocatedUniformLimitUp.mk I S M W r' e' g' h' c' p' n') :=
          congrArg some
            (congrArg (fun z => LocatedUniformLimitUp.mk I S M z r' e' g' h' c' p' n')
              (locatedUniformLimit_decode_encode W))
        _ = some (LocatedUniformLimitUp.mk I S M W R e' g' h' c' p' n') :=
          congrArg some
            (congrArg (fun z => LocatedUniformLimitUp.mk I S M W z e' g' h' c' p' n')
              (locatedUniformLimit_decode_encode R))
        _ = some (LocatedUniformLimitUp.mk I S M W R E g' h' c' p' n') :=
          congrArg some
            (congrArg (fun z => LocatedUniformLimitUp.mk I S M W R z g' h' c' p' n')
              (locatedUniformLimit_decode_encode E))
        _ = some (LocatedUniformLimitUp.mk I S M W R E G h' c' p' n') :=
          congrArg some
            (congrArg (fun z => LocatedUniformLimitUp.mk I S M W R E z h' c' p' n')
              (locatedUniformLimit_decode_encode G))
        _ = some (LocatedUniformLimitUp.mk I S M W R E G H c' p' n') :=
          congrArg some
            (congrArg (fun z => LocatedUniformLimitUp.mk I S M W R E G z c' p' n')
              (locatedUniformLimit_decode_encode H))
        _ = some (LocatedUniformLimitUp.mk I S M W R E G H C p' n') :=
          congrArg some
            (congrArg (fun z => LocatedUniformLimitUp.mk I S M W R E G H z p' n')
              (locatedUniformLimit_decode_encode C))
        _ = some (LocatedUniformLimitUp.mk I S M W R E G H C P n') :=
          congrArg some
            (congrArg (fun z => LocatedUniformLimitUp.mk I S M W R E G H C z n')
              (locatedUniformLimit_decode_encode P))
        _ = some (LocatedUniformLimitUp.mk I S M W R E G H C P N) :=
          congrArg some
            (congrArg (fun z => LocatedUniformLimitUp.mk I S M W R E G H C P z)
              (locatedUniformLimit_decode_encode N))

private theorem locatedUniformLimitToEventFlow_injective {x y : LocatedUniformLimitUp} :
    locatedUniformLimitToEventFlow x = locatedUniformLimitToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedUniformLimitFromEventFlow (locatedUniformLimitToEventFlow x) =
        locatedUniformLimitFromEventFlow (locatedUniformLimitToEventFlow y) :=
    congrArg locatedUniformLimitFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (locatedUniformLimit_round_trip x).symm
      (Eq.trans hread (locatedUniformLimit_round_trip y)))

instance locatedUniformLimitBHistCarrier : BHistCarrier LocatedUniformLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedUniformLimitToEventFlow
  fromEventFlow := locatedUniformLimitFromEventFlow

instance locatedUniformLimitChapterTasteGate : ChapterTasteGate LocatedUniformLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedUniformLimitFromEventFlow (locatedUniformLimitToEventFlow x) = some x
    exact locatedUniformLimit_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locatedUniformLimitToEventFlow_injective heq)

theorem LocatedUniformLimitTasteGate_single_carrier_alignment :
    (∀ h : BHist, locatedUniformLimitDecodeBHist (locatedUniformLimitEncodeBHist h) = h) ∧
      (∀ x : LocatedUniformLimitUp,
        locatedUniformLimitFromEventFlow (locatedUniformLimitToEventFlow x) = some x) ∧
        (∀ x y : LocatedUniformLimitUp,
          locatedUniformLimitToEventFlow x = locatedUniformLimitToEventFlow y → x = y) ∧
          locatedUniformLimitEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact locatedUniformLimit_decode_encode
  · constructor
    · exact locatedUniformLimit_round_trip
    · constructor
      · intro x y heq
        exact locatedUniformLimitToEventFlow_injective heq
      · rfl

end BEDC.Derived.LocatedUniformLimitUp
