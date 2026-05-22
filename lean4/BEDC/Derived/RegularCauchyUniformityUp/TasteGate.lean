import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyUniformityUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyUniformityUp : Type where
  | mk (R W D E H C P N : BHist) : RegularCauchyUniformityUp
  deriving DecidableEq

def regularCauchyUniformityEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyUniformityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyUniformityEncodeBHist h

def regularCauchyUniformityDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyUniformityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyUniformityDecodeBHist tail)

theorem RegularCauchyUniformityTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      regularCauchyUniformityDecodeBHist (regularCauchyUniformityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyUniformityFields : RegularCauchyUniformityUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyUniformityUp.mk R W D E H C P N => [R, W, D, E, H, C, P, N]

def regularCauchyUniformityToEventFlow : RegularCauchyUniformityUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularCauchyUniformityFields x).map regularCauchyUniformityEncodeBHist

def regularCauchyUniformityFromEventFlow : EventFlow -> Option RegularCauchyUniformityUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | R :: rest0 =>
      match rest0 with
      | [] => none
      | W :: rest1 =>
          match rest1 with
          | [] => none
          | D :: rest2 =>
              match rest2 with
              | [] => none
              | E :: rest3 =>
                  match rest3 with
                  | [] => none
                  | H :: rest4 =>
                      match rest4 with
                      | [] => none
                      | C :: rest5 =>
                          match rest5 with
                          | [] => none
                          | P :: rest6 =>
                              match rest6 with
                              | [] => none
                              | N :: rest7 =>
                                  match rest7 with
                                  | [] =>
                                      some
                                        (RegularCauchyUniformityUp.mk
                                          (regularCauchyUniformityDecodeBHist R)
                                          (regularCauchyUniformityDecodeBHist W)
                                          (regularCauchyUniformityDecodeBHist D)
                                          (regularCauchyUniformityDecodeBHist E)
                                          (regularCauchyUniformityDecodeBHist H)
                                          (regularCauchyUniformityDecodeBHist C)
                                          (regularCauchyUniformityDecodeBHist P)
                                          (regularCauchyUniformityDecodeBHist N))
                                  | _ :: _ => none

theorem RegularCauchyUniformityTasteGate_single_carrier_alignment_round_trip :
    forall x : RegularCauchyUniformityUp,
      regularCauchyUniformityFromEventFlow (regularCauchyUniformityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R W D E H C P N =>
      change
        some
          (RegularCauchyUniformityUp.mk
            (regularCauchyUniformityDecodeBHist (regularCauchyUniformityEncodeBHist R))
            (regularCauchyUniformityDecodeBHist (regularCauchyUniformityEncodeBHist W))
            (regularCauchyUniformityDecodeBHist (regularCauchyUniformityEncodeBHist D))
            (regularCauchyUniformityDecodeBHist (regularCauchyUniformityEncodeBHist E))
            (regularCauchyUniformityDecodeBHist (regularCauchyUniformityEncodeBHist H))
            (regularCauchyUniformityDecodeBHist (regularCauchyUniformityEncodeBHist C))
            (regularCauchyUniformityDecodeBHist (regularCauchyUniformityEncodeBHist P))
            (regularCauchyUniformityDecodeBHist (regularCauchyUniformityEncodeBHist N))) =
          some (RegularCauchyUniformityUp.mk R W D E H C P N)
      rw [RegularCauchyUniformityTasteGate_single_carrier_alignment_decode_encode R,
        RegularCauchyUniformityTasteGate_single_carrier_alignment_decode_encode W,
        RegularCauchyUniformityTasteGate_single_carrier_alignment_decode_encode D,
        RegularCauchyUniformityTasteGate_single_carrier_alignment_decode_encode E,
        RegularCauchyUniformityTasteGate_single_carrier_alignment_decode_encode H,
        RegularCauchyUniformityTasteGate_single_carrier_alignment_decode_encode C,
        RegularCauchyUniformityTasteGate_single_carrier_alignment_decode_encode P,
        RegularCauchyUniformityTasteGate_single_carrier_alignment_decode_encode N]

theorem RegularCauchyUniformityTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyUniformityUp} :
    regularCauchyUniformityToEventFlow x = regularCauchyUniformityToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyUniformityFromEventFlow (regularCauchyUniformityToEventFlow x) =
        regularCauchyUniformityFromEventFlow (regularCauchyUniformityToEventFlow y) :=
    congrArg regularCauchyUniformityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RegularCauchyUniformityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyUniformityTasteGate_single_carrier_alignment_round_trip y)))

theorem RegularCauchyUniformityTasteGate_single_carrier_alignment_field_faithful :
    forall x y : RegularCauchyUniformityUp,
      regularCauchyUniformityFields x = regularCauchyUniformityFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R1 W1 D1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk R2 W2 D2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance regularCauchyUniformityBHistCarrier : BHistCarrier RegularCauchyUniformityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyUniformityToEventFlow
  fromEventFlow := regularCauchyUniformityFromEventFlow

instance regularCauchyUniformityChapterTasteGate : ChapterTasteGate RegularCauchyUniformityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyUniformityFromEventFlow (regularCauchyUniformityToEventFlow x) = some x
    exact RegularCauchyUniformityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RegularCauchyUniformityTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance regularCauchyUniformityFieldFaithful : FieldFaithful RegularCauchyUniformityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyUniformityFields
  field_faithful := RegularCauchyUniformityTasteGate_single_carrier_alignment_field_faithful

instance regularCauchyUniformityNontrivial : Nontrivial RegularCauchyUniformityUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyUniformityUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchyUniformityUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem RegularCauchyUniformityTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RegularCauchyUniformityUp) ∧
      Nonempty (FieldFaithful RegularCauchyUniformityUp) ∧
        Nonempty (Nontrivial RegularCauchyUniformityUp) ∧
          (∀ h : BHist,
            regularCauchyUniformityDecodeBHist (regularCauchyUniformityEncodeBHist h) = h) ∧
            (∀ x : RegularCauchyUniformityUp,
              regularCauchyUniformityFromEventFlow (regularCauchyUniformityToEventFlow x) =
                some x) ∧
              (∀ x y : RegularCauchyUniformityUp,
                regularCauchyUniformityToEventFlow x = regularCauchyUniformityToEventFlow y ->
                  x = y) ∧
                regularCauchyUniformityEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨regularCauchyUniformityChapterTasteGate⟩
  · constructor
    · exact ⟨regularCauchyUniformityFieldFaithful⟩
    · constructor
      · exact ⟨regularCauchyUniformityNontrivial⟩
      · constructor
        · exact RegularCauchyUniformityTasteGate_single_carrier_alignment_decode_encode
        · constructor
          · exact RegularCauchyUniformityTasteGate_single_carrier_alignment_round_trip
          · constructor
            · intro x y heq
              exact RegularCauchyUniformityTasteGate_single_carrier_alignment_toEventFlow_injective heq
            · rfl

end BEDC.Derived.RegularCauchyUniformityUp.TasteGate
