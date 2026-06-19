import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyEvenOddSubstreamsUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyEvenOddSubstreamsUp : Type where
  | mk (S E O D R A B H C P N : BHist) : RegularCauchyEvenOddSubstreamsUp
  deriving DecidableEq

def regularCauchyEvenOddSubstreamsFields :
    RegularCauchyEvenOddSubstreamsUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyEvenOddSubstreamsUp.mk S E O D R A B H C P N =>
      [S, E, O, D, R, A, B, H, C, P, N]

def regularCauchyEvenOddSubstreamsEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyEvenOddSubstreamsEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyEvenOddSubstreamsEncodeBHist h

def regularCauchyEvenOddSubstreamsDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyEvenOddSubstreamsDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyEvenOddSubstreamsDecodeBHist tail)

private theorem RegularCauchyEvenOddSubstreamsTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      regularCauchyEvenOddSubstreamsDecodeBHist
        (regularCauchyEvenOddSubstreamsEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyEvenOddSubstreamsToEventFlow :
    RegularCauchyEvenOddSubstreamsUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyEvenOddSubstreamsUp.mk S E O D R A B H C P N =>
      [regularCauchyEvenOddSubstreamsEncodeBHist S,
        regularCauchyEvenOddSubstreamsEncodeBHist E,
        regularCauchyEvenOddSubstreamsEncodeBHist O,
        regularCauchyEvenOddSubstreamsEncodeBHist D,
        regularCauchyEvenOddSubstreamsEncodeBHist R,
        regularCauchyEvenOddSubstreamsEncodeBHist A,
        regularCauchyEvenOddSubstreamsEncodeBHist B,
        regularCauchyEvenOddSubstreamsEncodeBHist H,
        regularCauchyEvenOddSubstreamsEncodeBHist C,
        regularCauchyEvenOddSubstreamsEncodeBHist P,
        regularCauchyEvenOddSubstreamsEncodeBHist N]

private def regularCauchyEvenOddSubstreamsEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      regularCauchyEvenOddSubstreamsEventAtDefault index rest

def regularCauchyEvenOddSubstreamsDecodeEventFlow
    (ef : EventFlow) : RegularCauchyEvenOddSubstreamsUp :=
  -- BEDC touchpoint anchor: BHist BMark
  RegularCauchyEvenOddSubstreamsUp.mk
    (regularCauchyEvenOddSubstreamsDecodeBHist
      (regularCauchyEvenOddSubstreamsEventAtDefault 0 ef))
    (regularCauchyEvenOddSubstreamsDecodeBHist
      (regularCauchyEvenOddSubstreamsEventAtDefault 1 ef))
    (regularCauchyEvenOddSubstreamsDecodeBHist
      (regularCauchyEvenOddSubstreamsEventAtDefault 2 ef))
    (regularCauchyEvenOddSubstreamsDecodeBHist
      (regularCauchyEvenOddSubstreamsEventAtDefault 3 ef))
    (regularCauchyEvenOddSubstreamsDecodeBHist
      (regularCauchyEvenOddSubstreamsEventAtDefault 4 ef))
    (regularCauchyEvenOddSubstreamsDecodeBHist
      (regularCauchyEvenOddSubstreamsEventAtDefault 5 ef))
    (regularCauchyEvenOddSubstreamsDecodeBHist
      (regularCauchyEvenOddSubstreamsEventAtDefault 6 ef))
    (regularCauchyEvenOddSubstreamsDecodeBHist
      (regularCauchyEvenOddSubstreamsEventAtDefault 7 ef))
    (regularCauchyEvenOddSubstreamsDecodeBHist
      (regularCauchyEvenOddSubstreamsEventAtDefault 8 ef))
    (regularCauchyEvenOddSubstreamsDecodeBHist
      (regularCauchyEvenOddSubstreamsEventAtDefault 9 ef))
    (regularCauchyEvenOddSubstreamsDecodeBHist
      (regularCauchyEvenOddSubstreamsEventAtDefault 10 ef))

def regularCauchyEvenOddSubstreamsFromEventFlow
    (ef : EventFlow) : Option RegularCauchyEvenOddSubstreamsUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some (regularCauchyEvenOddSubstreamsDecodeEventFlow ef)

private theorem RegularCauchyEvenOddSubstreamsTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchyEvenOddSubstreamsUp,
      regularCauchyEvenOddSubstreamsFromEventFlow
        (regularCauchyEvenOddSubstreamsToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S E O D R A B H C P N =>
      change
        some
          (RegularCauchyEvenOddSubstreamsUp.mk
            (regularCauchyEvenOddSubstreamsDecodeBHist
              (regularCauchyEvenOddSubstreamsEncodeBHist S))
            (regularCauchyEvenOddSubstreamsDecodeBHist
              (regularCauchyEvenOddSubstreamsEncodeBHist E))
            (regularCauchyEvenOddSubstreamsDecodeBHist
              (regularCauchyEvenOddSubstreamsEncodeBHist O))
            (regularCauchyEvenOddSubstreamsDecodeBHist
              (regularCauchyEvenOddSubstreamsEncodeBHist D))
            (regularCauchyEvenOddSubstreamsDecodeBHist
              (regularCauchyEvenOddSubstreamsEncodeBHist R))
            (regularCauchyEvenOddSubstreamsDecodeBHist
              (regularCauchyEvenOddSubstreamsEncodeBHist A))
            (regularCauchyEvenOddSubstreamsDecodeBHist
              (regularCauchyEvenOddSubstreamsEncodeBHist B))
            (regularCauchyEvenOddSubstreamsDecodeBHist
              (regularCauchyEvenOddSubstreamsEncodeBHist H))
            (regularCauchyEvenOddSubstreamsDecodeBHist
              (regularCauchyEvenOddSubstreamsEncodeBHist C))
            (regularCauchyEvenOddSubstreamsDecodeBHist
              (regularCauchyEvenOddSubstreamsEncodeBHist P))
            (regularCauchyEvenOddSubstreamsDecodeBHist
              (regularCauchyEvenOddSubstreamsEncodeBHist N))) =
          some (RegularCauchyEvenOddSubstreamsUp.mk S E O D R A B H C P N)
      rw [RegularCauchyEvenOddSubstreamsTasteGate_single_carrier_alignment_decode_encode S,
        RegularCauchyEvenOddSubstreamsTasteGate_single_carrier_alignment_decode_encode E,
        RegularCauchyEvenOddSubstreamsTasteGate_single_carrier_alignment_decode_encode O,
        RegularCauchyEvenOddSubstreamsTasteGate_single_carrier_alignment_decode_encode D,
        RegularCauchyEvenOddSubstreamsTasteGate_single_carrier_alignment_decode_encode R,
        RegularCauchyEvenOddSubstreamsTasteGate_single_carrier_alignment_decode_encode A,
        RegularCauchyEvenOddSubstreamsTasteGate_single_carrier_alignment_decode_encode B,
        RegularCauchyEvenOddSubstreamsTasteGate_single_carrier_alignment_decode_encode H,
        RegularCauchyEvenOddSubstreamsTasteGate_single_carrier_alignment_decode_encode C,
        RegularCauchyEvenOddSubstreamsTasteGate_single_carrier_alignment_decode_encode P,
        RegularCauchyEvenOddSubstreamsTasteGate_single_carrier_alignment_decode_encode N]

private theorem
    RegularCauchyEvenOddSubstreamsTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyEvenOddSubstreamsUp} :
    regularCauchyEvenOddSubstreamsToEventFlow x =
        regularCauchyEvenOddSubstreamsToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyEvenOddSubstreamsFromEventFlow
          (regularCauchyEvenOddSubstreamsToEventFlow x) =
        regularCauchyEvenOddSubstreamsFromEventFlow
          (regularCauchyEvenOddSubstreamsToEventFlow y) :=
    congrArg regularCauchyEvenOddSubstreamsFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyEvenOddSubstreamsTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyEvenOddSubstreamsTasteGate_single_carrier_alignment_round_trip y)))

private theorem
    RegularCauchyEvenOddSubstreamsTasteGate_single_carrier_alignment_fields_injective :
    ∀ x y : RegularCauchyEvenOddSubstreamsUp,
      regularCauchyEvenOddSubstreamsFields x =
        regularCauchyEvenOddSubstreamsFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk S₁ E₁ O₁ D₁ R₁ A₁ B₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk S₂ E₂ O₂ D₂ R₂ A₂ B₂ H₂ C₂ P₂ N₂ =>
          simp only [regularCauchyEvenOddSubstreamsFields] at h
          injection h with hS t1
          injection t1 with hE t2
          injection t2 with hO t3
          injection t3 with hD t4
          injection t4 with hR t5
          injection t5 with hA t6
          injection t6 with hB t7
          injection t7 with hH t8
          injection t8 with hC t9
          injection t9 with hP t10
          injection t10 with hN _
          subst hS
          subst hE
          subst hO
          subst hD
          subst hR
          subst hA
          subst hB
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance regularCauchyEvenOddSubstreamsBHistCarrier :
    BHistCarrier RegularCauchyEvenOddSubstreamsUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyEvenOddSubstreamsToEventFlow
  fromEventFlow := regularCauchyEvenOddSubstreamsFromEventFlow

instance regularCauchyEvenOddSubstreamsChapterTasteGate :
    ChapterTasteGate RegularCauchyEvenOddSubstreamsUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyEvenOddSubstreamsFromEventFlow
        (regularCauchyEvenOddSubstreamsToEventFlow x) = some x
    exact RegularCauchyEvenOddSubstreamsTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegularCauchyEvenOddSubstreamsTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

instance regularCauchyEvenOddSubstreamsFieldFaithful :
    FieldFaithful RegularCauchyEvenOddSubstreamsUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyEvenOddSubstreamsFields
  field_faithful :=
    RegularCauchyEvenOddSubstreamsTasteGate_single_carrier_alignment_fields_injective

theorem RegularCauchyEvenOddSubstreamsTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyEvenOddSubstreamsDecodeBHist
        (regularCauchyEvenOddSubstreamsEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyEvenOddSubstreamsUp,
        regularCauchyEvenOddSubstreamsFromEventFlow
          (regularCauchyEvenOddSubstreamsToEventFlow x) = some x) ∧
        (∀ x y : RegularCauchyEvenOddSubstreamsUp,
          regularCauchyEvenOddSubstreamsFields x =
              regularCauchyEvenOddSubstreamsFields y →
            x = y) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  exact
    ⟨RegularCauchyEvenOddSubstreamsTasteGate_single_carrier_alignment_decode_encode,
      RegularCauchyEvenOddSubstreamsTasteGate_single_carrier_alignment_round_trip,
      RegularCauchyEvenOddSubstreamsTasteGate_single_carrier_alignment_fields_injective⟩

end BEDC.Derived.RegularCauchyEvenOddSubstreamsUp.TasteGate
