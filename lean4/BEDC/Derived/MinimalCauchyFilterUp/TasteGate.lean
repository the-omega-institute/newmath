import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MinimalCauchyFilterUp
namespace TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MinimalCauchyFilterUp : Type where
  | mk (F S R T D E H C P N : BHist) : MinimalCauchyFilterUp
  deriving DecidableEq

def minimalCauchyFilterEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: minimalCauchyFilterEncodeBHist h
  | BHist.e1 h => BMark.b1 :: minimalCauchyFilterEncodeBHist h

def minimalCauchyFilterDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (minimalCauchyFilterDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (minimalCauchyFilterDecodeBHist tail)

private theorem minimalCauchyFilter_decode_encode_bhist :
    forall h : BHist,
      minimalCauchyFilterDecodeBHist (minimalCauchyFilterEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def minimalCauchyFilterFields : MinimalCauchyFilterUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MinimalCauchyFilterUp.mk F S R T D E H C P N => [F, S, R, T, D, E, H, C, P, N]

def minimalCauchyFilterToEventFlow : MinimalCauchyFilterUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (minimalCauchyFilterFields x).map minimalCauchyFilterEncodeBHist

def minimalCauchyFilterFromEventFlow : EventFlow -> Option MinimalCauchyFilterUp
  -- BEDC touchpoint anchor: BHist BMark
  | F :: restF =>
      match restF with
      | S :: restS =>
          match restS with
          | R :: restR =>
              match restR with
              | T :: restT =>
                  match restT with
                  | D :: restD =>
                      match restD with
                      | E :: restE =>
                          match restE with
                          | H :: restH =>
                              match restH with
                              | C :: restC =>
                                  match restC with
                                  | P :: restP =>
                                      match restP with
                                      | N :: restN =>
                                          match restN with
                                          | [] =>
                                              some
                                                (MinimalCauchyFilterUp.mk
                                                  (minimalCauchyFilterDecodeBHist F)
                                                  (minimalCauchyFilterDecodeBHist S)
                                                  (minimalCauchyFilterDecodeBHist R)
                                                  (minimalCauchyFilterDecodeBHist T)
                                                  (minimalCauchyFilterDecodeBHist D)
                                                  (minimalCauchyFilterDecodeBHist E)
                                                  (minimalCauchyFilterDecodeBHist H)
                                                  (minimalCauchyFilterDecodeBHist C)
                                                  (minimalCauchyFilterDecodeBHist P)
                                                  (minimalCauchyFilterDecodeBHist N))
                                          | _ :: _ => none
                                      | [] => none
                                  | [] => none
                              | [] => none
                          | [] => none
                      | [] => none
                  | [] => none
              | [] => none
          | [] => none
      | [] => none
  | [] => none

private theorem minimalCauchyFilter_mk_congr
    {F F' S S' R R' T T' D D' E E' H H' C C' P P' N N' : BHist}
    (hF : F' = F) (hS : S' = S) (hR : R' = R) (hT : T' = T)
    (hD : D' = D) (hE : E' = E) (hH : H' = H) (hC : C' = C)
    (hP : P' = P) (hN : N' = N) :
    MinimalCauchyFilterUp.mk F' S' R' T' D' E' H' C' P' N' =
      MinimalCauchyFilterUp.mk F S R T D E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hF
  cases hS
  cases hR
  cases hT
  cases hD
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem minimalCauchyFilter_round_trip :
    forall x : MinimalCauchyFilterUp,
      minimalCauchyFilterFromEventFlow (minimalCauchyFilterToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F S R T D E H C P N =>
      exact
        congrArg some
          (minimalCauchyFilter_mk_congr
            (minimalCauchyFilter_decode_encode_bhist F)
            (minimalCauchyFilter_decode_encode_bhist S)
            (minimalCauchyFilter_decode_encode_bhist R)
            (minimalCauchyFilter_decode_encode_bhist T)
            (minimalCauchyFilter_decode_encode_bhist D)
            (minimalCauchyFilter_decode_encode_bhist E)
            (minimalCauchyFilter_decode_encode_bhist H)
            (minimalCauchyFilter_decode_encode_bhist C)
            (minimalCauchyFilter_decode_encode_bhist P)
            (minimalCauchyFilter_decode_encode_bhist N))

private theorem minimalCauchyFilterToEventFlow_injective
    {x y : MinimalCauchyFilterUp} :
    minimalCauchyFilterToEventFlow x = minimalCauchyFilterToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      minimalCauchyFilterFromEventFlow (minimalCauchyFilterToEventFlow x) =
        minimalCauchyFilterFromEventFlow (minimalCauchyFilterToEventFlow y) :=
    congrArg minimalCauchyFilterFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (minimalCauchyFilter_round_trip x).symm
      (Eq.trans hread (minimalCauchyFilter_round_trip y)))

private theorem minimalCauchyFilter_field_faithful :
    forall x y : MinimalCauchyFilterUp,
      minimalCauchyFilterFields x = minimalCauchyFilterFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F S R T D E H C P N =>
      cases y with
      | mk F' S' R' T' D' E' H' C' P' N' =>
          cases hfields
          rfl

instance minimalCauchyFilterBHistCarrier :
    BHistCarrier MinimalCauchyFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := minimalCauchyFilterToEventFlow
  fromEventFlow := minimalCauchyFilterFromEventFlow

instance minimalCauchyFilterChapterTasteGate :
    ChapterTasteGate MinimalCauchyFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change minimalCauchyFilterFromEventFlow (minimalCauchyFilterToEventFlow x) = some x
    exact minimalCauchyFilter_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (minimalCauchyFilterToEventFlow_injective heq)

instance minimalCauchyFilterFieldFaithful :
    FieldFaithful MinimalCauchyFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := minimalCauchyFilterFields
  field_faithful := minimalCauchyFilter_field_faithful

instance minimalCauchyFilterNontrivial :
    BEDC.Meta.TasteGate.Nontrivial MinimalCauchyFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MinimalCauchyFilterUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MinimalCauchyFilterUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MinimalCauchyFilterUp :=
  -- BEDC touchpoint anchor: BHist BMark
  minimalCauchyFilterChapterTasteGate

theorem MinimalCauchyFilterTasteGate_single_carrier_alignment :
    (forall h : BHist,
        minimalCauchyFilterDecodeBHist (minimalCauchyFilterEncodeBHist h) = h) /\
      (forall x : MinimalCauchyFilterUp,
        minimalCauchyFilterFromEventFlow (minimalCauchyFilterToEventFlow x) = some x) /\
      (forall x y : MinimalCauchyFilterUp,
        minimalCauchyFilterToEventFlow x =
          minimalCauchyFilterToEventFlow y -> x = y) /\
      minimalCauchyFilterEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  constructor
  · exact minimalCauchyFilter_decode_encode_bhist
  constructor
  · exact minimalCauchyFilter_round_trip
  constructor
  · intro x y heq
    exact minimalCauchyFilterToEventFlow_injective heq
  · rfl

end TasteGate
end BEDC.Derived.MinimalCauchyFilterUp
