import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyFilterRealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyFilterRealUp : Type where
  | mk (F S Q D E H C P N : BHist) : RegularCauchyFilterRealUp
  deriving DecidableEq

def regularCauchyFilterRealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyFilterRealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyFilterRealEncodeBHist h

def regularCauchyFilterRealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyFilterRealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyFilterRealDecodeBHist tail)

private theorem RegularCauchyFilterRealTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, regularCauchyFilterRealDecodeBHist
      (regularCauchyFilterRealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def RegularCauchyFilterRealTasteGate_single_carrier_alignment_fields :
    RegularCauchyFilterRealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyFilterRealUp.mk F S Q D E H C P N => [F, S, Q, D, E, H, C, P, N]

def RegularCauchyFilterRealTasteGate_single_carrier_alignment_toEventFlow :
    RegularCauchyFilterRealUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (RegularCauchyFilterRealTasteGate_single_carrier_alignment_fields x).map
      regularCauchyFilterRealEncodeBHist

def RegularCauchyFilterRealTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option RegularCauchyFilterRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun eventFlow =>
    match eventFlow with
    | [F, S, Q, D, E, H, C, P, N] =>
        some
          (RegularCauchyFilterRealUp.mk
            (regularCauchyFilterRealDecodeBHist F)
            (regularCauchyFilterRealDecodeBHist S)
            (regularCauchyFilterRealDecodeBHist Q)
            (regularCauchyFilterRealDecodeBHist D)
            (regularCauchyFilterRealDecodeBHist E)
            (regularCauchyFilterRealDecodeBHist H)
            (regularCauchyFilterRealDecodeBHist C)
            (regularCauchyFilterRealDecodeBHist P)
            (regularCauchyFilterRealDecodeBHist N))
    | _ => none

def RegularCauchyFilterRealTasteGate_single_carrier_alignment_carrier :
    BHistCarrier RegularCauchyFilterRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := RegularCauchyFilterRealTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := RegularCauchyFilterRealTasteGate_single_carrier_alignment_fromEventFlow

instance RegularCauchyFilterRealTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier RegularCauchyFilterRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  RegularCauchyFilterRealTasteGate_single_carrier_alignment_carrier

private theorem RegularCauchyFilterRealTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchyFilterRealUp,
      RegularCauchyFilterRealTasteGate_single_carrier_alignment_fromEventFlow
          (RegularCauchyFilterRealTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk F S Q D E H C P N =>
      change
        some
            (RegularCauchyFilterRealUp.mk
              (regularCauchyFilterRealDecodeBHist (regularCauchyFilterRealEncodeBHist F))
              (regularCauchyFilterRealDecodeBHist (regularCauchyFilterRealEncodeBHist S))
              (regularCauchyFilterRealDecodeBHist (regularCauchyFilterRealEncodeBHist Q))
              (regularCauchyFilterRealDecodeBHist (regularCauchyFilterRealEncodeBHist D))
              (regularCauchyFilterRealDecodeBHist (regularCauchyFilterRealEncodeBHist E))
              (regularCauchyFilterRealDecodeBHist (regularCauchyFilterRealEncodeBHist H))
              (regularCauchyFilterRealDecodeBHist (regularCauchyFilterRealEncodeBHist C))
              (regularCauchyFilterRealDecodeBHist (regularCauchyFilterRealEncodeBHist P))
              (regularCauchyFilterRealDecodeBHist (regularCauchyFilterRealEncodeBHist N))) =
          some (RegularCauchyFilterRealUp.mk F S Q D E H C P N)
      rw [RegularCauchyFilterRealTasteGate_single_carrier_alignment_decode_encode F]
      rw [RegularCauchyFilterRealTasteGate_single_carrier_alignment_decode_encode S]
      rw [RegularCauchyFilterRealTasteGate_single_carrier_alignment_decode_encode Q]
      rw [RegularCauchyFilterRealTasteGate_single_carrier_alignment_decode_encode D]
      rw [RegularCauchyFilterRealTasteGate_single_carrier_alignment_decode_encode E]
      rw [RegularCauchyFilterRealTasteGate_single_carrier_alignment_decode_encode H]
      rw [RegularCauchyFilterRealTasteGate_single_carrier_alignment_decode_encode C]
      rw [RegularCauchyFilterRealTasteGate_single_carrier_alignment_decode_encode P]
      rw [RegularCauchyFilterRealTasteGate_single_carrier_alignment_decode_encode N]

private theorem RegularCauchyFilterRealTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyFilterRealUp} :
    RegularCauchyFilterRealTasteGate_single_carrier_alignment_toEventFlow x =
        RegularCauchyFilterRealTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          RegularCauchyFilterRealTasteGate_single_carrier_alignment_fromEventFlow
              (RegularCauchyFilterRealTasteGate_single_carrier_alignment_toEventFlow x) :=
        (RegularCauchyFilterRealTasteGate_single_carrier_alignment_round_trip x).symm
      _ =
          RegularCauchyFilterRealTasteGate_single_carrier_alignment_fromEventFlow
              (RegularCauchyFilterRealTasteGate_single_carrier_alignment_toEventFlow y) :=
        congrArg RegularCauchyFilterRealTasteGate_single_carrier_alignment_fromEventFlow hxy
      _ = some y := RegularCauchyFilterRealTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

private theorem RegularCauchyFilterRealTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : RegularCauchyFilterRealUp,
      RegularCauchyFilterRealTasteGate_single_carrier_alignment_fields x =
          RegularCauchyFilterRealTasteGate_single_carrier_alignment_fields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F₁ S₁ Q₁ D₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk F₂ S₂ Q₂ D₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

def RegularCauchyFilterRealTasteGate_single_carrier_alignment_gate :
    @ChapterTasteGate RegularCauchyFilterRealUp
      RegularCauchyFilterRealTasteGate_single_carrier_alignment_carrier where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    exact RegularCauchyFilterRealTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RegularCauchyFilterRealTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance RegularCauchyFilterRealTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate RegularCauchyFilterRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  RegularCauchyFilterRealTasteGate_single_carrier_alignment_gate

instance RegularCauchyFilterRealTasteGate_single_carrier_alignment_FieldFaithful :
    FieldFaithful RegularCauchyFilterRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := RegularCauchyFilterRealTasteGate_single_carrier_alignment_fields
  field_faithful := RegularCauchyFilterRealTasteGate_single_carrier_alignment_field_faithful

theorem RegularCauchyFilterRealTasteGate_single_carrier_alignment :
    (forall h : BHist, regularCauchyFilterRealDecodeBHist
      (regularCauchyFilterRealEncodeBHist h) = h) ∧
      RegularCauchyFilterRealTasteGate_single_carrier_alignment_fields
          (RegularCauchyFilterRealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] ∧
          regularCauchyFilterRealEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨RegularCauchyFilterRealTasteGate_single_carrier_alignment_decode_encode,
      ⟨rfl, rfl⟩⟩

end BEDC.Derived.RegularCauchyFilterRealUp
