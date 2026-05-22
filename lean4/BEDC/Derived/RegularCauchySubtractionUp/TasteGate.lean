import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchySubtractionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchySubtractionUp : Type where
  | mk : (X Y G A W D E S H C P N : BHist) → RegularCauchySubtractionUp
  deriving DecidableEq

def regularCauchySubtractionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchySubtractionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchySubtractionEncodeBHist h

def regularCauchySubtractionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchySubtractionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchySubtractionDecodeBHist tail)

private theorem regularCauchySubtractionDecode_encode_bhist :
    ∀ h : BHist,
      regularCauchySubtractionDecodeBHist
        (regularCauchySubtractionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchySubtractionToEventFlow : RegularCauchySubtractionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchySubtractionUp.mk X Y G A W D E S H C P N =>
      [[BMark.b0],
        regularCauchySubtractionEncodeBHist X,
        [BMark.b1, BMark.b0],
        regularCauchySubtractionEncodeBHist Y,
        [BMark.b1, BMark.b1, BMark.b0],
        regularCauchySubtractionEncodeBHist G,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchySubtractionEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchySubtractionEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchySubtractionEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchySubtractionEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        regularCauchySubtractionEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        regularCauchySubtractionEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        regularCauchySubtractionEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchySubtractionEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchySubtractionEncodeBHist N]

def RegularCauchySubtractionUpTasteGate_single_carrier_alignment_read_rows :
    EventFlow → Option (List BHist)
  -- BEDC touchpoint anchor: BHist BMark
  | [] => some []
  | _tag :: row :: rest =>
      match RegularCauchySubtractionUpTasteGate_single_carrier_alignment_read_rows rest with
      | some rows => some (regularCauchySubtractionDecodeBHist row :: rows)
      | none => none
  | _ :: [] => none

def RegularCauchySubtractionUpTasteGate_single_carrier_alignment_from_rows :
    List BHist → Option RegularCauchySubtractionUp
  -- BEDC touchpoint anchor: BHist BMark
  | X :: rest1 =>
      match rest1 with
      | Y :: rest2 =>
          match rest2 with
          | G :: rest3 =>
              match rest3 with
              | A :: rest4 =>
                  match rest4 with
                  | W :: rest5 =>
                      match rest5 with
                      | D :: rest6 =>
                          match rest6 with
                          | E :: rest7 =>
                              match rest7 with
                              | S :: rest8 =>
                                  match rest8 with
                                  | H :: rest9 =>
                                      match rest9 with
                                      | C :: rest10 =>
                                          match rest10 with
                                          | P :: rest11 =>
                                              match rest11 with
                                              | N :: rest12 =>
                                                  match rest12 with
                                                  | [] =>
                                                      some
                                                        (RegularCauchySubtractionUp.mk
                                                          X Y G A W D E S H C P N)
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
      | [] => none
  | [] => none

def regularCauchySubtractionFromEventFlow
    (flow : EventFlow) : Option RegularCauchySubtractionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match RegularCauchySubtractionUpTasteGate_single_carrier_alignment_read_rows flow with
  | some rows => RegularCauchySubtractionUpTasteGate_single_carrier_alignment_from_rows rows
  | none => none

def regularCauchySubtractionFields :
    RegularCauchySubtractionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchySubtractionUp.mk X Y G A W D E S H C P N =>
      [X, Y, G, A, W, D, E, S, H, C, P, N]

private theorem regularCauchySubtraction_round_trip :
    ∀ x : RegularCauchySubtractionUp,
      regularCauchySubtractionFromEventFlow
        (regularCauchySubtractionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Y G A W D E S H C P N =>
      change
        some
          (RegularCauchySubtractionUp.mk
            (regularCauchySubtractionDecodeBHist
              (regularCauchySubtractionEncodeBHist X))
            (regularCauchySubtractionDecodeBHist
              (regularCauchySubtractionEncodeBHist Y))
            (regularCauchySubtractionDecodeBHist
              (regularCauchySubtractionEncodeBHist G))
            (regularCauchySubtractionDecodeBHist
              (regularCauchySubtractionEncodeBHist A))
            (regularCauchySubtractionDecodeBHist
              (regularCauchySubtractionEncodeBHist W))
            (regularCauchySubtractionDecodeBHist
              (regularCauchySubtractionEncodeBHist D))
            (regularCauchySubtractionDecodeBHist
              (regularCauchySubtractionEncodeBHist E))
            (regularCauchySubtractionDecodeBHist
              (regularCauchySubtractionEncodeBHist S))
            (regularCauchySubtractionDecodeBHist
              (regularCauchySubtractionEncodeBHist H))
            (regularCauchySubtractionDecodeBHist
              (regularCauchySubtractionEncodeBHist C))
            (regularCauchySubtractionDecodeBHist
              (regularCauchySubtractionEncodeBHist P))
            (regularCauchySubtractionDecodeBHist
              (regularCauchySubtractionEncodeBHist N))) =
          some (RegularCauchySubtractionUp.mk X Y G A W D E S H C P N)
      rw [regularCauchySubtractionDecode_encode_bhist X,
        regularCauchySubtractionDecode_encode_bhist Y,
        regularCauchySubtractionDecode_encode_bhist G,
        regularCauchySubtractionDecode_encode_bhist A,
        regularCauchySubtractionDecode_encode_bhist W,
        regularCauchySubtractionDecode_encode_bhist D,
        regularCauchySubtractionDecode_encode_bhist E,
        regularCauchySubtractionDecode_encode_bhist S,
        regularCauchySubtractionDecode_encode_bhist H,
        regularCauchySubtractionDecode_encode_bhist C,
        regularCauchySubtractionDecode_encode_bhist P,
        regularCauchySubtractionDecode_encode_bhist N]

private theorem regularCauchySubtractionToEventFlow_injective
    {x y : RegularCauchySubtractionUp} :
    regularCauchySubtractionToEventFlow x =
      regularCauchySubtractionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchySubtractionFromEventFlow
          (regularCauchySubtractionToEventFlow x) =
        regularCauchySubtractionFromEventFlow
          (regularCauchySubtractionToEventFlow y) :=
    congrArg regularCauchySubtractionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchySubtraction_round_trip x).symm
      (Eq.trans hread (regularCauchySubtraction_round_trip y)))

private theorem regularCauchySubtractionFields_faithful :
    ∀ x y : RegularCauchySubtractionUp,
      regularCauchySubtractionFields x = regularCauchySubtractionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk X1 Y1 G1 A1 W1 D1 E1 S1 H1 C1 P1 N1 =>
      cases y with
      | mk X2 Y2 G2 A2 W2 D2 E2 S2 H2 C2 P2 N2 =>
          cases h
          rfl

instance regularCauchySubtractionBHistCarrier :
    BHistCarrier RegularCauchySubtractionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchySubtractionToEventFlow
  fromEventFlow := regularCauchySubtractionFromEventFlow

instance regularCauchySubtractionChapterTasteGate :
    ChapterTasteGate RegularCauchySubtractionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchySubtractionFromEventFlow
        (regularCauchySubtractionToEventFlow x) = some x
    exact regularCauchySubtraction_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchySubtractionToEventFlow_injective heq)

instance regularCauchySubtractionFieldFaithful :
    FieldFaithful RegularCauchySubtractionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchySubtractionFields
  field_faithful := regularCauchySubtractionFields_faithful

instance regularCauchySubtractionNontrivial :
    Nontrivial RegularCauchySubtractionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchySubtractionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      RegularCauchySubtractionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegularCauchySubtractionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  inferInstance

theorem RegularCauchySubtractionUpTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchySubtractionDecodeBHist
        (regularCauchySubtractionEncodeBHist h) = h) ∧
      (∀ x : RegularCauchySubtractionUp,
        regularCauchySubtractionFromEventFlow
          (regularCauchySubtractionToEventFlow x) = some x) ∧
        (∀ x y : RegularCauchySubtractionUp,
          regularCauchySubtractionToEventFlow x =
            regularCauchySubtractionToEventFlow y → x = y) ∧
          regularCauchySubtractionEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∀ x y : RegularCauchySubtractionUp,
              regularCauchySubtractionFields x =
                regularCauchySubtractionFields y → x = y) ∧
              (∃ x y : RegularCauchySubtractionUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact regularCauchySubtractionDecode_encode_bhist
  · constructor
    · exact regularCauchySubtraction_round_trip
    · constructor
      · intro x y heq
        exact regularCauchySubtractionToEventFlow_injective heq
      · constructor
        · rfl
        · constructor
          · exact regularCauchySubtractionFields_faithful
          · exact
              ⟨RegularCauchySubtractionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty,
                RegularCauchySubtractionUp.mk (BHist.e0 BHist.Empty) BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
                by
                  intro h
                  cases h⟩

end BEDC.Derived.RegularCauchySubtractionUp
