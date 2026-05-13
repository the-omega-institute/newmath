import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.StationaryWindowNaturalityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive StationaryWindowNaturalityUp : Type where
  | mk (Q S R D E W H C P K : BHist) : StationaryWindowNaturalityUp
  deriving DecidableEq

def stationaryWindowNaturalityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: stationaryWindowNaturalityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: stationaryWindowNaturalityEncodeBHist h

def stationaryWindowNaturalityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (stationaryWindowNaturalityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (stationaryWindowNaturalityDecodeBHist tail)

private theorem stationaryWindowNaturalityDecode_encode_bhist :
    ∀ h : BHist,
      stationaryWindowNaturalityDecodeBHist
        (stationaryWindowNaturalityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def stationaryWindowNaturalityToEventFlow :
    StationaryWindowNaturalityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | StationaryWindowNaturalityUp.mk Q S R D E W H C P K =>
      [[BMark.b0],
        stationaryWindowNaturalityEncodeBHist Q,
        [BMark.b1, BMark.b0],
        stationaryWindowNaturalityEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b0],
        stationaryWindowNaturalityEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        stationaryWindowNaturalityEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        stationaryWindowNaturalityEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        stationaryWindowNaturalityEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        stationaryWindowNaturalityEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        stationaryWindowNaturalityEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        stationaryWindowNaturalityEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        stationaryWindowNaturalityEncodeBHist K]

def stationaryWindowNaturalityFromEventFlow :
    EventFlow → Option StationaryWindowNaturalityUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | Q :: rest1 =>
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
                      | R :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | D :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | E :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | W :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | H :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | C :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | P :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 ::
                                                                              rest18 =>
                                                                              match
                                                                                rest18
                                                                              with
                                                                              | [] =>
                                                                                  none
                                                                              | K ::
                                                                                  rest19 =>
                                                                                  match
                                                                                    rest19
                                                                                  with
                                                                                  | [] =>
                                                                                      some
                                                                                        (StationaryWindowNaturalityUp.mk
                                                                                          (stationaryWindowNaturalityDecodeBHist
                                                                                            Q)
                                                                                          (stationaryWindowNaturalityDecodeBHist
                                                                                            S)
                                                                                          (stationaryWindowNaturalityDecodeBHist
                                                                                            R)
                                                                                          (stationaryWindowNaturalityDecodeBHist
                                                                                            D)
                                                                                          (stationaryWindowNaturalityDecodeBHist
                                                                                            E)
                                                                                          (stationaryWindowNaturalityDecodeBHist
                                                                                            W)
                                                                                          (stationaryWindowNaturalityDecodeBHist
                                                                                            H)
                                                                                          (stationaryWindowNaturalityDecodeBHist
                                                                                            C)
                                                                                          (stationaryWindowNaturalityDecodeBHist
                                                                                            P)
                                                                                          (stationaryWindowNaturalityDecodeBHist
                                                                                            K))
                                                                                  | _ ::
                                                                                      _ =>
                                                                                      none

private theorem stationaryWindowNaturality_round_trip :
    ∀ x : StationaryWindowNaturalityUp,
      stationaryWindowNaturalityFromEventFlow
        (stationaryWindowNaturalityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q S R D E W H C P K =>
      change
        some
          (StationaryWindowNaturalityUp.mk
            (stationaryWindowNaturalityDecodeBHist
              (stationaryWindowNaturalityEncodeBHist Q))
            (stationaryWindowNaturalityDecodeBHist
              (stationaryWindowNaturalityEncodeBHist S))
            (stationaryWindowNaturalityDecodeBHist
              (stationaryWindowNaturalityEncodeBHist R))
            (stationaryWindowNaturalityDecodeBHist
              (stationaryWindowNaturalityEncodeBHist D))
            (stationaryWindowNaturalityDecodeBHist
              (stationaryWindowNaturalityEncodeBHist E))
            (stationaryWindowNaturalityDecodeBHist
              (stationaryWindowNaturalityEncodeBHist W))
            (stationaryWindowNaturalityDecodeBHist
              (stationaryWindowNaturalityEncodeBHist H))
            (stationaryWindowNaturalityDecodeBHist
              (stationaryWindowNaturalityEncodeBHist C))
            (stationaryWindowNaturalityDecodeBHist
              (stationaryWindowNaturalityEncodeBHist P))
            (stationaryWindowNaturalityDecodeBHist
              (stationaryWindowNaturalityEncodeBHist K))) =
          some (StationaryWindowNaturalityUp.mk Q S R D E W H C P K)
      rw [stationaryWindowNaturalityDecode_encode_bhist Q,
        stationaryWindowNaturalityDecode_encode_bhist S,
        stationaryWindowNaturalityDecode_encode_bhist R,
        stationaryWindowNaturalityDecode_encode_bhist D,
        stationaryWindowNaturalityDecode_encode_bhist E,
        stationaryWindowNaturalityDecode_encode_bhist W,
        stationaryWindowNaturalityDecode_encode_bhist H,
        stationaryWindowNaturalityDecode_encode_bhist C,
        stationaryWindowNaturalityDecode_encode_bhist P,
        stationaryWindowNaturalityDecode_encode_bhist K]

private theorem stationaryWindowNaturalityToEventFlow_injective
    {x y : StationaryWindowNaturalityUp} :
    stationaryWindowNaturalityToEventFlow x =
      stationaryWindowNaturalityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      stationaryWindowNaturalityFromEventFlow
          (stationaryWindowNaturalityToEventFlow x) =
        stationaryWindowNaturalityFromEventFlow
          (stationaryWindowNaturalityToEventFlow y) :=
    congrArg stationaryWindowNaturalityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (stationaryWindowNaturality_round_trip x).symm
      (Eq.trans hread (stationaryWindowNaturality_round_trip y)))

instance stationaryWindowNaturalityBHistCarrier :
    BHistCarrier StationaryWindowNaturalityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := stationaryWindowNaturalityToEventFlow
  fromEventFlow := stationaryWindowNaturalityFromEventFlow

instance stationaryWindowNaturalityChapterTasteGate :
    ChapterTasteGate StationaryWindowNaturalityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      stationaryWindowNaturalityFromEventFlow
        (stationaryWindowNaturalityToEventFlow x) = some x
    exact stationaryWindowNaturality_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (stationaryWindowNaturalityToEventFlow_injective heq)

def taste_gate : ChapterTasteGate StationaryWindowNaturalityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  stationaryWindowNaturalityChapterTasteGate

instance stationaryWindowNaturalityNontrivial :
    Nontrivial StationaryWindowNaturalityUp where
  witness_pair :=
    ⟨StationaryWindowNaturalityUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      StationaryWindowNaturalityUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

instance stationaryWindowNaturalityFieldFaithful :
    FieldFaithful StationaryWindowNaturalityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields
    | StationaryWindowNaturalityUp.mk Q S R D E W H C P K =>
        [Q, S, R, D, E, W, H, C, P, K]
  field_faithful := by
    intro x y hfields
    cases x with
    | mk Q S R D E W H C P K =>
        cases y with
        | mk Q' S' R' D' E' W' H' C' P' K' =>
            injection hfields with hQ hTail0
            injection hTail0 with hS hTail1
            injection hTail1 with hR hTail2
            injection hTail2 with hD hTail3
            injection hTail3 with hE hTail4
            injection hTail4 with hW hTail5
            injection hTail5 with hH hTail6
            injection hTail6 with hC hTail7
            injection hTail7 with hP hTail8
            injection hTail8 with hK _hNil
            cases hQ
            cases hS
            cases hR
            cases hD
            cases hE
            cases hW
            cases hH
            cases hC
            cases hP
            cases hK
            rfl

theorem StationaryWindowNaturalityTasteGate_single_carrier_alignment :
    (∀ h : BHist, stationaryWindowNaturalityDecodeBHist
      (stationaryWindowNaturalityEncodeBHist h) = h) ∧
      (∀ x : StationaryWindowNaturalityUp,
        stationaryWindowNaturalityFromEventFlow
          (stationaryWindowNaturalityToEventFlow x) = some x) ∧
        (∀ x y : StationaryWindowNaturalityUp,
          stationaryWindowNaturalityToEventFlow x =
            stationaryWindowNaturalityToEventFlow y → x = y) ∧
          stationaryWindowNaturalityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact stationaryWindowNaturalityDecode_encode_bhist
  · constructor
    · exact stationaryWindowNaturality_round_trip
    · constructor
      · intro x y heq
        exact stationaryWindowNaturalityToEventFlow_injective heq
      · rfl

end BEDC.Derived.StationaryWindowNaturalityUp
