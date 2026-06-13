import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HyperbolicBusemannBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HyperbolicBusemannBoundaryUp : Type where
  | mk (D M O T R B L H C P N : BHist) : HyperbolicBusemannBoundaryUp

def hyperbolicBusemannBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hyperbolicBusemannBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hyperbolicBusemannBoundaryEncodeBHist h

def hyperbolicBusemannBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hyperbolicBusemannBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hyperbolicBusemannBoundaryDecodeBHist tail)

private theorem hyperbolicBusemannBoundaryDecode_encode_bhist :
    ∀ h : BHist,
      hyperbolicBusemannBoundaryDecodeBHist
          (hyperbolicBusemannBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def hyperbolicBusemannBoundaryFields : HyperbolicBusemannBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HyperbolicBusemannBoundaryUp.mk D M O T R B L H C P N =>
      [D, M, O, T, R, B, L, H, C, P, N]

def hyperbolicBusemannBoundaryToEventFlow : HyperbolicBusemannBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (hyperbolicBusemannBoundaryFields x).map hyperbolicBusemannBoundaryEncodeBHist

def hyperbolicBusemannBoundaryFromEventFlow :
    EventFlow → Option HyperbolicBusemannBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | D :: rest0 =>
      match rest0 with
      | [] => none
      | M :: rest1 =>
          match rest1 with
          | [] => none
          | O :: rest2 =>
              match rest2 with
              | [] => none
              | T :: rest3 =>
                  match rest3 with
                  | [] => none
                  | R :: rest4 =>
                      match rest4 with
                      | [] => none
                      | B :: rest5 =>
                          match rest5 with
                          | [] => none
                          | L :: rest6 =>
                              match rest6 with
                              | [] => none
                              | H :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | C :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | P :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | N :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (HyperbolicBusemannBoundaryUp.mk
                                                      (hyperbolicBusemannBoundaryDecodeBHist D)
                                                      (hyperbolicBusemannBoundaryDecodeBHist M)
                                                      (hyperbolicBusemannBoundaryDecodeBHist O)
                                                      (hyperbolicBusemannBoundaryDecodeBHist T)
                                                      (hyperbolicBusemannBoundaryDecodeBHist R)
                                                      (hyperbolicBusemannBoundaryDecodeBHist B)
                                                      (hyperbolicBusemannBoundaryDecodeBHist L)
                                                      (hyperbolicBusemannBoundaryDecodeBHist H)
                                                      (hyperbolicBusemannBoundaryDecodeBHist C)
                                                      (hyperbolicBusemannBoundaryDecodeBHist P)
                                                      (hyperbolicBusemannBoundaryDecodeBHist N))
                                              | _ :: _ => none

private theorem hyperbolicBusemannBoundary_round_trip :
    ∀ x : HyperbolicBusemannBoundaryUp,
      hyperbolicBusemannBoundaryFromEventFlow
          (hyperbolicBusemannBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D M O T R B L H C P N =>
      change
        some
          (HyperbolicBusemannBoundaryUp.mk
            (hyperbolicBusemannBoundaryDecodeBHist
              (hyperbolicBusemannBoundaryEncodeBHist D))
            (hyperbolicBusemannBoundaryDecodeBHist
              (hyperbolicBusemannBoundaryEncodeBHist M))
            (hyperbolicBusemannBoundaryDecodeBHist
              (hyperbolicBusemannBoundaryEncodeBHist O))
            (hyperbolicBusemannBoundaryDecodeBHist
              (hyperbolicBusemannBoundaryEncodeBHist T))
            (hyperbolicBusemannBoundaryDecodeBHist
              (hyperbolicBusemannBoundaryEncodeBHist R))
            (hyperbolicBusemannBoundaryDecodeBHist
              (hyperbolicBusemannBoundaryEncodeBHist B))
            (hyperbolicBusemannBoundaryDecodeBHist
              (hyperbolicBusemannBoundaryEncodeBHist L))
            (hyperbolicBusemannBoundaryDecodeBHist
              (hyperbolicBusemannBoundaryEncodeBHist H))
            (hyperbolicBusemannBoundaryDecodeBHist
              (hyperbolicBusemannBoundaryEncodeBHist C))
            (hyperbolicBusemannBoundaryDecodeBHist
              (hyperbolicBusemannBoundaryEncodeBHist P))
            (hyperbolicBusemannBoundaryDecodeBHist
              (hyperbolicBusemannBoundaryEncodeBHist N))) =
          some (HyperbolicBusemannBoundaryUp.mk D M O T R B L H C P N)
      rw [hyperbolicBusemannBoundaryDecode_encode_bhist D,
        hyperbolicBusemannBoundaryDecode_encode_bhist M,
        hyperbolicBusemannBoundaryDecode_encode_bhist O,
        hyperbolicBusemannBoundaryDecode_encode_bhist T,
        hyperbolicBusemannBoundaryDecode_encode_bhist R,
        hyperbolicBusemannBoundaryDecode_encode_bhist B,
        hyperbolicBusemannBoundaryDecode_encode_bhist L,
        hyperbolicBusemannBoundaryDecode_encode_bhist H,
        hyperbolicBusemannBoundaryDecode_encode_bhist C,
        hyperbolicBusemannBoundaryDecode_encode_bhist P,
        hyperbolicBusemannBoundaryDecode_encode_bhist N]

private theorem hyperbolicBusemannBoundaryToEventFlow_injective
    {x y : HyperbolicBusemannBoundaryUp} :
    hyperbolicBusemannBoundaryToEventFlow x =
        hyperbolicBusemannBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hyperbolicBusemannBoundaryFromEventFlow
          (hyperbolicBusemannBoundaryToEventFlow x) =
        hyperbolicBusemannBoundaryFromEventFlow
          (hyperbolicBusemannBoundaryToEventFlow y) :=
    congrArg hyperbolicBusemannBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (hyperbolicBusemannBoundary_round_trip x).symm
      (Eq.trans hread (hyperbolicBusemannBoundary_round_trip y)))

private theorem hyperbolicBusemannBoundary_fields_faithful :
    ∀ x y : HyperbolicBusemannBoundaryUp,
      hyperbolicBusemannBoundaryFields x = hyperbolicBusemannBoundaryFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk D1 M1 O1 T1 R1 B1 L1 H1 C1 P1 N1 =>
      cases y with
      | mk D2 M2 O2 T2 R2 B2 L2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance hyperbolicBusemannBoundaryBHistCarrier :
    BHistCarrier HyperbolicBusemannBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hyperbolicBusemannBoundaryToEventFlow
  fromEventFlow := hyperbolicBusemannBoundaryFromEventFlow

instance hyperbolicBusemannBoundaryChapterTasteGate :
    ChapterTasteGate HyperbolicBusemannBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      hyperbolicBusemannBoundaryFromEventFlow
          (hyperbolicBusemannBoundaryToEventFlow x) = some x
    exact hyperbolicBusemannBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (hyperbolicBusemannBoundaryToEventFlow_injective heq)

instance hyperbolicBusemannBoundaryFieldFaithful :
    FieldFaithful HyperbolicBusemannBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := hyperbolicBusemannBoundaryFields
  field_faithful := hyperbolicBusemannBoundary_fields_faithful

instance hyperbolicBusemannBoundaryNontrivial : Nontrivial HyperbolicBusemannBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨HyperbolicBusemannBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      HyperbolicBusemannBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

theorem HyperbolicBusemannBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      hyperbolicBusemannBoundaryDecodeBHist
          (hyperbolicBusemannBoundaryEncodeBHist h) = h) ∧
      (∀ x : HyperbolicBusemannBoundaryUp,
        hyperbolicBusemannBoundaryFromEventFlow
            (hyperbolicBusemannBoundaryToEventFlow x) = some x) ∧
        (∀ x y : HyperbolicBusemannBoundaryUp,
          hyperbolicBusemannBoundaryToEventFlow x =
              hyperbolicBusemannBoundaryToEventFlow y → x = y) ∧
          hyperbolicBusemannBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact hyperbolicBusemannBoundaryDecode_encode_bhist
  · constructor
    · exact hyperbolicBusemannBoundary_round_trip
    · constructor
      · intro x y heq
        exact hyperbolicBusemannBoundaryToEventFlow_injective heq
      · rfl

end BEDC.Derived.HyperbolicBusemannBoundaryUp
