import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BusemannBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BusemannBoundaryUp : Type where
  | mk (X o R D L H C P N : BHist) : BusemannBoundaryUp
  deriving DecidableEq

def busemannBoundaryEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: busemannBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: busemannBoundaryEncodeBHist h

def busemannBoundaryDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (busemannBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (busemannBoundaryDecodeBHist tail)

private theorem busemannBoundaryDecode_encode_bhist :
    forall h : BHist, busemannBoundaryDecodeBHist (busemannBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def busemannBoundaryFields : BusemannBoundaryUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BusemannBoundaryUp.mk X o R D L H C P N => [X, o, R, D, L, H, C, P, N]

def busemannBoundaryToEventFlow : BusemannBoundaryUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (busemannBoundaryFields x).map busemannBoundaryEncodeBHist

def busemannBoundaryFromEventFlow : EventFlow -> Option BusemannBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | X :: rest0 =>
      match rest0 with
      | [] => none
      | o :: rest1 =>
          match rest1 with
          | [] => none
          | R :: rest2 =>
              match rest2 with
              | [] => none
              | D :: rest3 =>
                  match rest3 with
                  | [] => none
                  | L :: rest4 =>
                      match rest4 with
                      | [] => none
                      | H :: rest5 =>
                          match rest5 with
                          | [] => none
                          | C :: rest6 =>
                              match rest6 with
                              | [] => none
                              | P :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | N :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (BusemannBoundaryUp.mk
                                              (busemannBoundaryDecodeBHist X)
                                              (busemannBoundaryDecodeBHist o)
                                              (busemannBoundaryDecodeBHist R)
                                              (busemannBoundaryDecodeBHist D)
                                              (busemannBoundaryDecodeBHist L)
                                              (busemannBoundaryDecodeBHist H)
                                              (busemannBoundaryDecodeBHist C)
                                              (busemannBoundaryDecodeBHist P)
                                              (busemannBoundaryDecodeBHist N))
                                      | _ :: _ => none

private theorem busemannBoundary_round_trip :
    forall x : BusemannBoundaryUp,
      busemannBoundaryFromEventFlow (busemannBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X o R D L H C P N =>
      change
        some
          (BusemannBoundaryUp.mk
            (busemannBoundaryDecodeBHist (busemannBoundaryEncodeBHist X))
            (busemannBoundaryDecodeBHist (busemannBoundaryEncodeBHist o))
            (busemannBoundaryDecodeBHist (busemannBoundaryEncodeBHist R))
            (busemannBoundaryDecodeBHist (busemannBoundaryEncodeBHist D))
            (busemannBoundaryDecodeBHist (busemannBoundaryEncodeBHist L))
            (busemannBoundaryDecodeBHist (busemannBoundaryEncodeBHist H))
            (busemannBoundaryDecodeBHist (busemannBoundaryEncodeBHist C))
            (busemannBoundaryDecodeBHist (busemannBoundaryEncodeBHist P))
            (busemannBoundaryDecodeBHist (busemannBoundaryEncodeBHist N))) =
          some (BusemannBoundaryUp.mk X o R D L H C P N)
      rw [busemannBoundaryDecode_encode_bhist X, busemannBoundaryDecode_encode_bhist o,
        busemannBoundaryDecode_encode_bhist R, busemannBoundaryDecode_encode_bhist D,
        busemannBoundaryDecode_encode_bhist L, busemannBoundaryDecode_encode_bhist H,
        busemannBoundaryDecode_encode_bhist C, busemannBoundaryDecode_encode_bhist P,
        busemannBoundaryDecode_encode_bhist N]

private theorem busemannBoundaryToEventFlow_injective {x y : BusemannBoundaryUp} :
    busemannBoundaryToEventFlow x = busemannBoundaryToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      busemannBoundaryFromEventFlow (busemannBoundaryToEventFlow x) =
        busemannBoundaryFromEventFlow (busemannBoundaryToEventFlow y) :=
    congrArg busemannBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (busemannBoundary_round_trip x).symm
      (Eq.trans hread (busemannBoundary_round_trip y)))

private theorem busemannBoundary_fields_faithful :
    forall x y : BusemannBoundaryUp, busemannBoundaryFields x = busemannBoundaryFields y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 o1 R1 D1 L1 H1 C1 P1 N1 =>
      cases y with
      | mk X2 o2 R2 D2 L2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance busemannBoundaryBHistCarrier : BHistCarrier BusemannBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := busemannBoundaryToEventFlow
  fromEventFlow := busemannBoundaryFromEventFlow

instance busemannBoundaryChapterTasteGate : ChapterTasteGate BusemannBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change busemannBoundaryFromEventFlow (busemannBoundaryToEventFlow x) = some x
    exact busemannBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (busemannBoundaryToEventFlow_injective heq)

instance busemannBoundaryFieldFaithful : FieldFaithful BusemannBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := busemannBoundaryFields
  field_faithful := busemannBoundary_fields_faithful

instance busemannBoundaryNontrivial : Nontrivial BusemannBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BusemannBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BusemannBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem BusemannBoundaryTasteGate_single_carrier_alignment :
    (forall h : BHist, busemannBoundaryDecodeBHist (busemannBoundaryEncodeBHist h) = h) ∧
      (forall x : BusemannBoundaryUp,
        busemannBoundaryFromEventFlow (busemannBoundaryToEventFlow x) = some x) ∧
        (forall x y : BusemannBoundaryUp,
          busemannBoundaryToEventFlow x = busemannBoundaryToEventFlow y -> x = y) ∧
          busemannBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact busemannBoundaryDecode_encode_bhist
  · constructor
    · exact busemannBoundary_round_trip
    · constructor
      · intro x y heq
        exact busemannBoundaryToEventFlow_injective heq
      · rfl

end BEDC.Derived.BusemannBoundaryUp
