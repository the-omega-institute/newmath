import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyMultiplicationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyMultiplicationUp : Type where
  | mk (X Y W D B E M Z H C P N : BHist) : RegularCauchyMultiplicationUp
  deriving DecidableEq

def regularCauchyMultiplicationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyMultiplicationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyMultiplicationEncodeBHist h

def regularCauchyMultiplicationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyMultiplicationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyMultiplicationDecodeBHist tail)

private theorem regularCauchyMultiplicationDecode_encode_bhist :
    ∀ h : BHist,
      regularCauchyMultiplicationDecodeBHist
        (regularCauchyMultiplicationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyMultiplicationFields :
    RegularCauchyMultiplicationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyMultiplicationUp.mk X Y W D B E M Z H C P N =>
      [X, Y, W, D, B, E, M, Z, H, C, P, N]

def regularCauchyMultiplicationToEventFlow :
    RegularCauchyMultiplicationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularCauchyMultiplicationFields x).map regularCauchyMultiplicationEncodeBHist

def regularCauchyMultiplicationFromEventFlow :
    EventFlow → Option RegularCauchyMultiplicationUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | X :: restY =>
      match restY with
      | [] => none
      | Y :: restW =>
          match restW with
          | [] => none
          | W :: restD =>
              match restD with
              | [] => none
              | D :: restB =>
                  match restB with
                  | [] => none
                  | B :: restE =>
                      match restE with
                      | [] => none
                      | E :: restM =>
                          match restM with
                          | [] => none
                          | M :: restZ =>
                              match restZ with
                              | [] => none
                              | Z :: restH =>
                                  match restH with
                                  | [] => none
                                  | H :: restC =>
                                      match restC with
                                      | [] => none
                                      | C :: restP =>
                                          match restP with
                                          | [] => none
                                          | P :: restN =>
                                              match restN with
                                              | [] => none
                                              | N :: rest =>
                                                  match rest with
                                                  | [] =>
                                                      some
                                                        (RegularCauchyMultiplicationUp.mk
                                                          (regularCauchyMultiplicationDecodeBHist X)
                                                          (regularCauchyMultiplicationDecodeBHist Y)
                                                          (regularCauchyMultiplicationDecodeBHist W)
                                                          (regularCauchyMultiplicationDecodeBHist D)
                                                          (regularCauchyMultiplicationDecodeBHist B)
                                                          (regularCauchyMultiplicationDecodeBHist E)
                                                          (regularCauchyMultiplicationDecodeBHist M)
                                                          (regularCauchyMultiplicationDecodeBHist Z)
                                                          (regularCauchyMultiplicationDecodeBHist H)
                                                          (regularCauchyMultiplicationDecodeBHist C)
                                                          (regularCauchyMultiplicationDecodeBHist P)
                                                          (regularCauchyMultiplicationDecodeBHist N))
                                                  | _ :: _ => none

private theorem regularCauchyMultiplication_round_trip :
    ∀ x : RegularCauchyMultiplicationUp,
      regularCauchyMultiplicationFromEventFlow
        (regularCauchyMultiplicationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Y W D B E M Z H C P N =>
      change
        some
          (RegularCauchyMultiplicationUp.mk
            (regularCauchyMultiplicationDecodeBHist
              (regularCauchyMultiplicationEncodeBHist X))
            (regularCauchyMultiplicationDecodeBHist
              (regularCauchyMultiplicationEncodeBHist Y))
            (regularCauchyMultiplicationDecodeBHist
              (regularCauchyMultiplicationEncodeBHist W))
            (regularCauchyMultiplicationDecodeBHist
              (regularCauchyMultiplicationEncodeBHist D))
            (regularCauchyMultiplicationDecodeBHist
              (regularCauchyMultiplicationEncodeBHist B))
            (regularCauchyMultiplicationDecodeBHist
              (regularCauchyMultiplicationEncodeBHist E))
            (regularCauchyMultiplicationDecodeBHist
              (regularCauchyMultiplicationEncodeBHist M))
            (regularCauchyMultiplicationDecodeBHist
              (regularCauchyMultiplicationEncodeBHist Z))
            (regularCauchyMultiplicationDecodeBHist
              (regularCauchyMultiplicationEncodeBHist H))
            (regularCauchyMultiplicationDecodeBHist
              (regularCauchyMultiplicationEncodeBHist C))
            (regularCauchyMultiplicationDecodeBHist
              (regularCauchyMultiplicationEncodeBHist P))
            (regularCauchyMultiplicationDecodeBHist
              (regularCauchyMultiplicationEncodeBHist N))) =
          some (RegularCauchyMultiplicationUp.mk X Y W D B E M Z H C P N)
      rw [regularCauchyMultiplicationDecode_encode_bhist X,
        regularCauchyMultiplicationDecode_encode_bhist Y,
        regularCauchyMultiplicationDecode_encode_bhist W,
        regularCauchyMultiplicationDecode_encode_bhist D,
        regularCauchyMultiplicationDecode_encode_bhist B,
        regularCauchyMultiplicationDecode_encode_bhist E,
        regularCauchyMultiplicationDecode_encode_bhist M,
        regularCauchyMultiplicationDecode_encode_bhist Z,
        regularCauchyMultiplicationDecode_encode_bhist H,
        regularCauchyMultiplicationDecode_encode_bhist C,
        regularCauchyMultiplicationDecode_encode_bhist P,
        regularCauchyMultiplicationDecode_encode_bhist N]

private theorem regularCauchyMultiplicationToEventFlow_injective
    {x y : RegularCauchyMultiplicationUp} :
    regularCauchyMultiplicationToEventFlow x =
      regularCauchyMultiplicationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyMultiplicationFromEventFlow
          (regularCauchyMultiplicationToEventFlow x) =
        regularCauchyMultiplicationFromEventFlow
          (regularCauchyMultiplicationToEventFlow y) :=
    congrArg regularCauchyMultiplicationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyMultiplication_round_trip x).symm
      (Eq.trans hread (regularCauchyMultiplication_round_trip y)))

private theorem regularCauchyMultiplicationFields_faithful :
    ∀ x y : RegularCauchyMultiplicationUp,
      regularCauchyMultiplicationFields x =
        regularCauchyMultiplicationFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk X1 Y1 W1 D1 B1 E1 M1 Z1 H1 C1 P1 N1 =>
      cases y with
      | mk X2 Y2 W2 D2 B2 E2 M2 Z2 H2 C2 P2 N2 =>
          cases h
          rfl

instance regularCauchyMultiplicationBHistCarrier :
    BHistCarrier RegularCauchyMultiplicationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyMultiplicationToEventFlow
  fromEventFlow := regularCauchyMultiplicationFromEventFlow

instance regularCauchyMultiplicationChapterTasteGate :
    ChapterTasteGate RegularCauchyMultiplicationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyMultiplicationFromEventFlow
        (regularCauchyMultiplicationToEventFlow x) = some x
    exact regularCauchyMultiplication_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyMultiplicationToEventFlow_injective heq)

instance regularCauchyMultiplicationFieldFaithful :
    FieldFaithful RegularCauchyMultiplicationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyMultiplicationFields
  field_faithful := regularCauchyMultiplicationFields_faithful

instance regularCauchyMultiplicationNontrivial :
    Nontrivial RegularCauchyMultiplicationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyMultiplicationUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchyMultiplicationUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegularCauchyMultiplicationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  inferInstance

namespace TasteGate

theorem RegularCauchyMultiplicationTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyMultiplicationDecodeBHist
        (regularCauchyMultiplicationEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyMultiplicationUp,
        regularCauchyMultiplicationFromEventFlow
          (regularCauchyMultiplicationToEventFlow x) = some x) ∧
        (∀ x y : RegularCauchyMultiplicationUp,
          regularCauchyMultiplicationToEventFlow x =
            regularCauchyMultiplicationToEventFlow y → x = y) ∧
          (∀ x y : RegularCauchyMultiplicationUp,
            regularCauchyMultiplicationFields x =
              regularCauchyMultiplicationFields y → x = y) ∧
            (∃ x y : RegularCauchyMultiplicationUp, x ≠ y) ∧
              regularCauchyMultiplicationEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact regularCauchyMultiplicationDecode_encode_bhist
  · constructor
    · exact regularCauchyMultiplication_round_trip
    · constructor
      · intro x y heq
        exact regularCauchyMultiplicationToEventFlow_injective heq
      · constructor
        · exact regularCauchyMultiplicationFields_faithful
        · constructor
          · exact
              ⟨RegularCauchyMultiplicationUp.mk BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty,
                RegularCauchyMultiplicationUp.mk (BHist.e0 BHist.Empty) BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
                by
                  intro h
                  cases h⟩
          · rfl

end TasteGate

end BEDC.Derived.RegularCauchyMultiplicationUp
