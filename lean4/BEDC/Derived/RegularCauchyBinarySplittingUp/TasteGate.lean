import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyBinarySplittingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyBinarySplittingUp : Type where
  | mk (W0 W1 D0 D1 R0 R1 A Sigma H C P N : BHist) :
      RegularCauchyBinarySplittingUp
  deriving DecidableEq

def regularCauchyBinarySplittingEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyBinarySplittingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyBinarySplittingEncodeBHist h

def regularCauchyBinarySplittingDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyBinarySplittingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyBinarySplittingDecodeBHist tail)

private theorem regularCauchyBinarySplitting_decode_encode :
    forall h : BHist,
      regularCauchyBinarySplittingDecodeBHist
        (regularCauchyBinarySplittingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyBinarySplittingFields :
    RegularCauchyBinarySplittingUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyBinarySplittingUp.mk W0 W1 D0 D1 R0 R1 A Sigma H C P N =>
      [W0, W1, D0, D1, R0, R1, A, Sigma, H, C, P, N]

def regularCauchyBinarySplittingToEventFlow :
    RegularCauchyBinarySplittingUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyBinarySplittingUp.mk W0 W1 D0 D1 R0 R1 A Sigma H C P N =>
      [[BMark.b0],
        regularCauchyBinarySplittingEncodeBHist W0,
        [BMark.b1],
        regularCauchyBinarySplittingEncodeBHist W1,
        [BMark.b0, BMark.b0],
        regularCauchyBinarySplittingEncodeBHist D0,
        [BMark.b0, BMark.b1],
        regularCauchyBinarySplittingEncodeBHist D1,
        [BMark.b1, BMark.b0],
        regularCauchyBinarySplittingEncodeBHist R0,
        [BMark.b1, BMark.b1],
        regularCauchyBinarySplittingEncodeBHist R1,
        [BMark.b0, BMark.b0, BMark.b0],
        regularCauchyBinarySplittingEncodeBHist A,
        [BMark.b0, BMark.b0, BMark.b1],
        regularCauchyBinarySplittingEncodeBHist Sigma,
        [BMark.b0, BMark.b1, BMark.b0],
        regularCauchyBinarySplittingEncodeBHist H,
        [BMark.b0, BMark.b1, BMark.b1],
        regularCauchyBinarySplittingEncodeBHist C,
        [BMark.b1, BMark.b0, BMark.b0],
        regularCauchyBinarySplittingEncodeBHist P,
        [BMark.b1, BMark.b0, BMark.b1],
        regularCauchyBinarySplittingEncodeBHist N]

private def regularCauchyBinarySplittingDecodePacket
    (W0 W1 D0 D1 R0 R1 A Sigma H C P N : RawEvent) :
    RegularCauchyBinarySplittingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  RegularCauchyBinarySplittingUp.mk
    (regularCauchyBinarySplittingDecodeBHist W0)
    (regularCauchyBinarySplittingDecodeBHist W1)
    (regularCauchyBinarySplittingDecodeBHist D0)
    (regularCauchyBinarySplittingDecodeBHist D1)
    (regularCauchyBinarySplittingDecodeBHist R0)
    (regularCauchyBinarySplittingDecodeBHist R1)
    (regularCauchyBinarySplittingDecodeBHist A)
    (regularCauchyBinarySplittingDecodeBHist Sigma)
    (regularCauchyBinarySplittingDecodeBHist H)
    (regularCauchyBinarySplittingDecodeBHist C)
    (regularCauchyBinarySplittingDecodeBHist P)
    (regularCauchyBinarySplittingDecodeBHist N)

def regularCauchyBinarySplittingFromEventFlow :
    EventFlow -> Option RegularCauchyBinarySplittingUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | W0 :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | W1 :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | D0 :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | D1 :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | R0 :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | R1 :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | A :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | Sigma :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | H :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | C :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | P :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] => none
                                                                                          | _tag11 :: rest22 =>
                                                                                              match rest22 with
                                                                                              | [] => none
                                                                                              | N :: rest23 =>
                                                                                                  match rest23 with
                                                                                                  | [] =>
                                                                                                      some
                                                                                                        (regularCauchyBinarySplittingDecodePacket
                                                                                                          W0
                                                                                                          W1
                                                                                                          D0
                                                                                                          D1
                                                                                                          R0
                                                                                                          R1
                                                                                                          A
                                                                                                          Sigma
                                                                                                          H
                                                                                                          C
                                                                                                          P
                                                                                                          N)
                                                                                                  | _ :: _ => none

private theorem regularCauchyBinarySplitting_round_trip :
    forall x : RegularCauchyBinarySplittingUp,
      regularCauchyBinarySplittingFromEventFlow
        (regularCauchyBinarySplittingToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk W0 W1 D0 D1 R0 R1 A Sigma H C P N =>
      change
        some
          (regularCauchyBinarySplittingDecodePacket
            (regularCauchyBinarySplittingEncodeBHist W0)
            (regularCauchyBinarySplittingEncodeBHist W1)
            (regularCauchyBinarySplittingEncodeBHist D0)
            (regularCauchyBinarySplittingEncodeBHist D1)
            (regularCauchyBinarySplittingEncodeBHist R0)
            (regularCauchyBinarySplittingEncodeBHist R1)
            (regularCauchyBinarySplittingEncodeBHist A)
            (regularCauchyBinarySplittingEncodeBHist Sigma)
            (regularCauchyBinarySplittingEncodeBHist H)
            (regularCauchyBinarySplittingEncodeBHist C)
            (regularCauchyBinarySplittingEncodeBHist P)
            (regularCauchyBinarySplittingEncodeBHist N)) =
          some (RegularCauchyBinarySplittingUp.mk W0 W1 D0 D1 R0 R1 A Sigma H C P N)
      unfold regularCauchyBinarySplittingDecodePacket
      rw [regularCauchyBinarySplitting_decode_encode W0,
        regularCauchyBinarySplitting_decode_encode W1,
        regularCauchyBinarySplitting_decode_encode D0,
        regularCauchyBinarySplitting_decode_encode D1,
        regularCauchyBinarySplitting_decode_encode R0,
        regularCauchyBinarySplitting_decode_encode R1,
        regularCauchyBinarySplitting_decode_encode A,
        regularCauchyBinarySplitting_decode_encode Sigma,
        regularCauchyBinarySplitting_decode_encode H,
        regularCauchyBinarySplitting_decode_encode C,
        regularCauchyBinarySplitting_decode_encode P,
        regularCauchyBinarySplitting_decode_encode N]

private theorem regularCauchyBinarySplittingToEventFlow_injective
    {x y : RegularCauchyBinarySplittingUp} :
    regularCauchyBinarySplittingToEventFlow x =
        regularCauchyBinarySplittingToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyBinarySplittingFromEventFlow
          (regularCauchyBinarySplittingToEventFlow x) =
        regularCauchyBinarySplittingFromEventFlow
          (regularCauchyBinarySplittingToEventFlow y) :=
    congrArg regularCauchyBinarySplittingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (regularCauchyBinarySplitting_round_trip x).symm
      (Eq.trans hread (regularCauchyBinarySplitting_round_trip y)))

instance regularCauchyBinarySplittingBHistCarrier :
    BHistCarrier RegularCauchyBinarySplittingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyBinarySplittingToEventFlow
  fromEventFlow := regularCauchyBinarySplittingFromEventFlow

instance regularCauchyBinarySplittingChapterTasteGate :
    ChapterTasteGate RegularCauchyBinarySplittingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyBinarySplittingFromEventFlow
        (regularCauchyBinarySplittingToEventFlow x) = some x
    exact regularCauchyBinarySplitting_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyBinarySplittingToEventFlow_injective heq)

private theorem regularCauchyBinarySplitting_field_faithful :
    forall x y : RegularCauchyBinarySplittingUp,
      regularCauchyBinarySplittingFields x = regularCauchyBinarySplittingFields y ->
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk W01 W11 D01 D11 R01 R11 A1 Sigma1 H1 C1 P1 N1 =>
      cases y with
      | mk W02 W12 D02 D12 R02 R12 A2 Sigma2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance regularCauchyBinarySplittingFieldFaithful :
    FieldFaithful RegularCauchyBinarySplittingUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyBinarySplittingFields
  field_faithful := regularCauchyBinarySplitting_field_faithful

instance regularCauchyBinarySplittingNontrivial :
    Nontrivial RegularCauchyBinarySplittingUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyBinarySplittingUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      RegularCauchyBinarySplittingUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem RegularCauchyBinarySplittingTasteGate_single_carrier_alignment :
    (forall h : BHist,
      regularCauchyBinarySplittingDecodeBHist
        (regularCauchyBinarySplittingEncodeBHist h) = h) ∧
      (forall x : RegularCauchyBinarySplittingUp,
        regularCauchyBinarySplittingFromEventFlow
          (regularCauchyBinarySplittingToEventFlow x) = some x) ∧
        (forall x y : RegularCauchyBinarySplittingUp,
          regularCauchyBinarySplittingToEventFlow x =
              regularCauchyBinarySplittingToEventFlow y ->
            x = y) ∧
          regularCauchyBinarySplittingEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨regularCauchyBinarySplitting_decode_encode,
      regularCauchyBinarySplitting_round_trip,
      by
        intro x y heq
        exact regularCauchyBinarySplittingToEventFlow_injective heq,
      rfl⟩

def taste_gate : ChapterTasteGate RegularCauchyBinarySplittingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyBinarySplittingChapterTasteGate

end BEDC.Derived.RegularCauchyBinarySplittingUp
