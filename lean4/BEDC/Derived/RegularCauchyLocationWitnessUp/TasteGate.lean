import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyLocationWitnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyLocationWitnessUp : Type where
  | mk (R S D W E H C P N : BHist) : RegularCauchyLocationWitnessUp
  deriving DecidableEq

def regularCauchyLocationWitnessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyLocationWitnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyLocationWitnessEncodeBHist h

def regularCauchyLocationWitnessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyLocationWitnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyLocationWitnessDecodeBHist tail)

private theorem RegularCauchyLocationWitnessUpTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      regularCauchyLocationWitnessDecodeBHist
          (regularCauchyLocationWitnessEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyLocationWitnessFields :
    RegularCauchyLocationWitnessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyLocationWitnessUp.mk R S D W E H C P N => [R, S, D, W, E, H, C, P, N]

def regularCauchyLocationWitnessToEventFlow :
    RegularCauchyLocationWitnessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularCauchyLocationWitnessFields x).map regularCauchyLocationWitnessEncodeBHist

private def regularCauchyLocationWitnessRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _ => event
  | Nat.succ _, [] => []
  | Nat.succ index, _ :: rest => regularCauchyLocationWitnessRawAt index rest

def regularCauchyLocationWitnessFromEventFlow
    (flow : EventFlow) : Option RegularCauchyLocationWitnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyLocationWitnessUp.mk
      (regularCauchyLocationWitnessDecodeBHist (regularCauchyLocationWitnessRawAt 0 flow))
      (regularCauchyLocationWitnessDecodeBHist (regularCauchyLocationWitnessRawAt 1 flow))
      (regularCauchyLocationWitnessDecodeBHist (regularCauchyLocationWitnessRawAt 2 flow))
      (regularCauchyLocationWitnessDecodeBHist (regularCauchyLocationWitnessRawAt 3 flow))
      (regularCauchyLocationWitnessDecodeBHist (regularCauchyLocationWitnessRawAt 4 flow))
      (regularCauchyLocationWitnessDecodeBHist (regularCauchyLocationWitnessRawAt 5 flow))
      (regularCauchyLocationWitnessDecodeBHist (regularCauchyLocationWitnessRawAt 6 flow))
      (regularCauchyLocationWitnessDecodeBHist (regularCauchyLocationWitnessRawAt 7 flow))
      (regularCauchyLocationWitnessDecodeBHist (regularCauchyLocationWitnessRawAt 8 flow)))

private theorem RegularCauchyLocationWitnessUpTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchyLocationWitnessUp,
      regularCauchyLocationWitnessFromEventFlow
          (regularCauchyLocationWitnessToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R S D W E H C P N =>
      change
        some
          (RegularCauchyLocationWitnessUp.mk
            (regularCauchyLocationWitnessDecodeBHist
              (regularCauchyLocationWitnessEncodeBHist R))
            (regularCauchyLocationWitnessDecodeBHist
              (regularCauchyLocationWitnessEncodeBHist S))
            (regularCauchyLocationWitnessDecodeBHist
              (regularCauchyLocationWitnessEncodeBHist D))
            (regularCauchyLocationWitnessDecodeBHist
              (regularCauchyLocationWitnessEncodeBHist W))
            (regularCauchyLocationWitnessDecodeBHist
              (regularCauchyLocationWitnessEncodeBHist E))
            (regularCauchyLocationWitnessDecodeBHist
              (regularCauchyLocationWitnessEncodeBHist H))
            (regularCauchyLocationWitnessDecodeBHist
              (regularCauchyLocationWitnessEncodeBHist C))
            (regularCauchyLocationWitnessDecodeBHist
              (regularCauchyLocationWitnessEncodeBHist P))
            (regularCauchyLocationWitnessDecodeBHist
              (regularCauchyLocationWitnessEncodeBHist N))) =
          some (RegularCauchyLocationWitnessUp.mk R S D W E H C P N)
      rw [RegularCauchyLocationWitnessUpTasteGate_single_carrier_alignment_decode_encode R,
        RegularCauchyLocationWitnessUpTasteGate_single_carrier_alignment_decode_encode S,
        RegularCauchyLocationWitnessUpTasteGate_single_carrier_alignment_decode_encode D,
        RegularCauchyLocationWitnessUpTasteGate_single_carrier_alignment_decode_encode W,
        RegularCauchyLocationWitnessUpTasteGate_single_carrier_alignment_decode_encode E,
        RegularCauchyLocationWitnessUpTasteGate_single_carrier_alignment_decode_encode H,
        RegularCauchyLocationWitnessUpTasteGate_single_carrier_alignment_decode_encode C,
        RegularCauchyLocationWitnessUpTasteGate_single_carrier_alignment_decode_encode P,
        RegularCauchyLocationWitnessUpTasteGate_single_carrier_alignment_decode_encode N]

private theorem RegularCauchyLocationWitnessUpTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyLocationWitnessUp} :
    regularCauchyLocationWitnessToEventFlow x =
        regularCauchyLocationWitnessToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyLocationWitnessFromEventFlow
          (regularCauchyLocationWitnessToEventFlow x) =
        regularCauchyLocationWitnessFromEventFlow
          (regularCauchyLocationWitnessToEventFlow y) :=
    congrArg regularCauchyLocationWitnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RegularCauchyLocationWitnessUpTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyLocationWitnessUpTasteGate_single_carrier_alignment_round_trip y)))

private theorem RegularCauchyLocationWitnessUpTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : RegularCauchyLocationWitnessUp,
      regularCauchyLocationWitnessFields x =
          regularCauchyLocationWitnessFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R₁ S₁ D₁ W₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk R₂ S₂ D₂ W₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance regularCauchyLocationWitnessBHistCarrier :
    BHistCarrier RegularCauchyLocationWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyLocationWitnessToEventFlow
  fromEventFlow := regularCauchyLocationWitnessFromEventFlow

instance regularCauchyLocationWitnessChapterTasteGate :
    ChapterTasteGate RegularCauchyLocationWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyLocationWitnessFromEventFlow
          (regularCauchyLocationWitnessToEventFlow x) =
        some x
    exact RegularCauchyLocationWitnessUpTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegularCauchyLocationWitnessUpTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance regularCauchyLocationWitnessFieldFaithful :
    FieldFaithful RegularCauchyLocationWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyLocationWitnessFields
  field_faithful :=
    RegularCauchyLocationWitnessUpTasteGate_single_carrier_alignment_field_faithful

instance regularCauchyLocationWitnessNontrivial :
    Nontrivial RegularCauchyLocationWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyLocationWitnessUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchyLocationWitnessUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegularCauchyLocationWitnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyLocationWitnessChapterTasteGate

theorem RegularCauchyLocationWitnessUpTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RegularCauchyLocationWitnessUp) ∧
      Nonempty (FieldFaithful RegularCauchyLocationWitnessUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial RegularCauchyLocationWitnessUp) ∧
          (∀ h : BHist,
            regularCauchyLocationWitnessDecodeBHist
                (regularCauchyLocationWitnessEncodeBHist h) =
              h) ∧
            (∀ x : RegularCauchyLocationWitnessUp,
              regularCauchyLocationWitnessFromEventFlow
                  (regularCauchyLocationWitnessToEventFlow x) =
                some x) ∧
              (∀ x y : RegularCauchyLocationWitnessUp,
                regularCauchyLocationWitnessToEventFlow x =
                    regularCauchyLocationWitnessToEventFlow y →
                  x = y) ∧
                regularCauchyLocationWitnessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate Nontrivial
  exact
    ⟨⟨regularCauchyLocationWitnessChapterTasteGate⟩,
      ⟨⟨regularCauchyLocationWitnessFieldFaithful⟩,
        ⟨⟨regularCauchyLocationWitnessNontrivial⟩,
          ⟨RegularCauchyLocationWitnessUpTasteGate_single_carrier_alignment_decode_encode,
            ⟨RegularCauchyLocationWitnessUpTasteGate_single_carrier_alignment_round_trip,
              ⟨(fun _ _ heq =>
                  RegularCauchyLocationWitnessUpTasteGate_single_carrier_alignment_toEventFlow_injective heq),
                rfl⟩⟩⟩⟩⟩⟩

end BEDC.Derived.RegularCauchyLocationWitnessUp
