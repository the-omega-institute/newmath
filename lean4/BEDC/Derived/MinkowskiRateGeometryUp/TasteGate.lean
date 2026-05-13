import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MinkowskiRateGeometryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MinkowskiRateGeometryUp : Type where
  | mk (G X R L D H C P N : BHist) : MinkowskiRateGeometryUp
  deriving DecidableEq

def minkowskiRateGeometryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: minkowskiRateGeometryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: minkowskiRateGeometryEncodeBHist h

def minkowskiRateGeometryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (minkowskiRateGeometryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (minkowskiRateGeometryDecodeBHist tail)

private theorem minkowskiRateGeometryDecode_encode_bhist :
    ∀ h : BHist,
      minkowskiRateGeometryDecodeBHist (minkowskiRateGeometryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def minkowskiRateGeometryToEventFlow : MinkowskiRateGeometryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MinkowskiRateGeometryUp.mk G X R L D H C P N =>
      [[BMark.b0],
        minkowskiRateGeometryEncodeBHist G,
        [BMark.b1, BMark.b0],
        minkowskiRateGeometryEncodeBHist X,
        [BMark.b1, BMark.b1, BMark.b0],
        minkowskiRateGeometryEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        minkowskiRateGeometryEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        minkowskiRateGeometryEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        minkowskiRateGeometryEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        minkowskiRateGeometryEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        minkowskiRateGeometryEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        minkowskiRateGeometryEncodeBHist N]

def minkowskiRateGeometryFromEventFlow :
    EventFlow → Option MinkowskiRateGeometryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | G :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | X :: rest3 =>
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
                              | L :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | D :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | H :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | C :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | P :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | N :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (MinkowskiRateGeometryUp.mk
                                                                                  (minkowskiRateGeometryDecodeBHist
                                                                                    G)
                                                                                  (minkowskiRateGeometryDecodeBHist
                                                                                    X)
                                                                                  (minkowskiRateGeometryDecodeBHist
                                                                                    R)
                                                                                  (minkowskiRateGeometryDecodeBHist
                                                                                    L)
                                                                                  (minkowskiRateGeometryDecodeBHist
                                                                                    D)
                                                                                  (minkowskiRateGeometryDecodeBHist
                                                                                    H)
                                                                                  (minkowskiRateGeometryDecodeBHist
                                                                                    C)
                                                                                  (minkowskiRateGeometryDecodeBHist
                                                                                    P)
                                                                                  (minkowskiRateGeometryDecodeBHist
                                                                                    N))
                                                                          | _ :: _ => none

private theorem minkowskiRateGeometry_round_trip :
    ∀ x : MinkowskiRateGeometryUp,
      minkowskiRateGeometryFromEventFlow (minkowskiRateGeometryToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk G X R L D H C P N =>
      change
        some
          (MinkowskiRateGeometryUp.mk
            (minkowskiRateGeometryDecodeBHist (minkowskiRateGeometryEncodeBHist G))
            (minkowskiRateGeometryDecodeBHist (minkowskiRateGeometryEncodeBHist X))
            (minkowskiRateGeometryDecodeBHist (minkowskiRateGeometryEncodeBHist R))
            (minkowskiRateGeometryDecodeBHist (minkowskiRateGeometryEncodeBHist L))
            (minkowskiRateGeometryDecodeBHist (minkowskiRateGeometryEncodeBHist D))
            (minkowskiRateGeometryDecodeBHist (minkowskiRateGeometryEncodeBHist H))
            (minkowskiRateGeometryDecodeBHist (minkowskiRateGeometryEncodeBHist C))
            (minkowskiRateGeometryDecodeBHist (minkowskiRateGeometryEncodeBHist P))
            (minkowskiRateGeometryDecodeBHist (minkowskiRateGeometryEncodeBHist N))) =
          some (MinkowskiRateGeometryUp.mk G X R L D H C P N)
      rw [minkowskiRateGeometryDecode_encode_bhist G,
        minkowskiRateGeometryDecode_encode_bhist X,
        minkowskiRateGeometryDecode_encode_bhist R,
        minkowskiRateGeometryDecode_encode_bhist L,
        minkowskiRateGeometryDecode_encode_bhist D,
        minkowskiRateGeometryDecode_encode_bhist H,
        minkowskiRateGeometryDecode_encode_bhist C,
        minkowskiRateGeometryDecode_encode_bhist P,
        minkowskiRateGeometryDecode_encode_bhist N]

private theorem minkowskiRateGeometryToEventFlow_injective
    {x y : MinkowskiRateGeometryUp} :
    minkowskiRateGeometryToEventFlow x =
      minkowskiRateGeometryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      minkowskiRateGeometryFromEventFlow (minkowskiRateGeometryToEventFlow x) =
        minkowskiRateGeometryFromEventFlow (minkowskiRateGeometryToEventFlow y) :=
    congrArg minkowskiRateGeometryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (minkowskiRateGeometry_round_trip x).symm
      (Eq.trans hread (minkowskiRateGeometry_round_trip y)))

instance minkowskiRateGeometryBHistCarrier :
    BHistCarrier MinkowskiRateGeometryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := minkowskiRateGeometryToEventFlow
  fromEventFlow := minkowskiRateGeometryFromEventFlow

instance minkowskiRateGeometryChapterTasteGate :
    ChapterTasteGate MinkowskiRateGeometryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      minkowskiRateGeometryFromEventFlow (minkowskiRateGeometryToEventFlow x) =
        some x
    exact minkowskiRateGeometry_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (minkowskiRateGeometryToEventFlow_injective heq)

def taste_gate : ChapterTasteGate MinkowskiRateGeometryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  minkowskiRateGeometryChapterTasteGate

instance minkowskiRateGeometryNontrivial : Nontrivial MinkowskiRateGeometryUp where
  witness_pair :=
    ⟨MinkowskiRateGeometryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MinkowskiRateGeometryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

instance minkowskiRateGeometryFieldFaithful :
    FieldFaithful MinkowskiRateGeometryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields
    | MinkowskiRateGeometryUp.mk G X R L D H C P N => [G, X, R, L, D, H, C, P, N]
  field_faithful := by
    intro x y hfields
    cases x with
    | mk G X R L D H C P N =>
        cases y with
        | mk G' X' R' L' D' H' C' P' N' =>
            injection hfields with hG hTail0
            injection hTail0 with hX hTail1
            injection hTail1 with hR hTail2
            injection hTail2 with hL hTail3
            injection hTail3 with hD hTail4
            injection hTail4 with hH hTail5
            injection hTail5 with hC hTail6
            injection hTail6 with hP hTail7
            injection hTail7 with hN _hNil
            cases hG
            cases hX
            cases hR
            cases hL
            cases hD
            cases hH
            cases hC
            cases hP
            cases hN
            rfl

theorem MinkowskiRateGeometryTasteGate_single_carrier_alignment :
    (∀ h : BHist, minkowskiRateGeometryDecodeBHist
      (minkowskiRateGeometryEncodeBHist h) = h) ∧
      (∀ x : MinkowskiRateGeometryUp,
        minkowskiRateGeometryFromEventFlow
          (minkowskiRateGeometryToEventFlow x) = some x) ∧
        (∀ x y : MinkowskiRateGeometryUp,
          minkowskiRateGeometryToEventFlow x =
            minkowskiRateGeometryToEventFlow y → x = y) ∧
          minkowskiRateGeometryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact minkowskiRateGeometryDecode_encode_bhist
  · constructor
    · exact minkowskiRateGeometry_round_trip
    · constructor
      · intro x y heq
        exact minkowskiRateGeometryToEventFlow_injective heq
      · rfl

end BEDC.Derived.MinkowskiRateGeometryUp
