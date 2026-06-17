import BEDC.Derived.RegularCauchyRingUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyRingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyRingUp : Type where
  | mk (A B WA WB DA DB S G M L RS RG RM RL ES EG EM EL H C P N : BHist) :
      RegularCauchyRingUp
  deriving DecidableEq

def regularCauchyRingEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyRingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyRingEncodeBHist h

def regularCauchyRingDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyRingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyRingDecodeBHist tail)

private theorem RegularCauchyRingTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, regularCauchyRingDecodeBHist (regularCauchyRingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def RegularCauchyRingTasteGate_single_carrier_alignment_fields :
    RegularCauchyRingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyRingUp.mk A B WA WB DA DB S G M L RS RG RM RL ES EG EM EL H C P N =>
      [A, B, WA, WB, DA, DB, S, G, M, L, RS, RG, RM, RL, ES, EG, EM, EL, H, C, P, N]

def RegularCauchyRingTasteGate_single_carrier_alignment_toEventFlow :
    RegularCauchyRingUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (RegularCauchyRingTasteGate_single_carrier_alignment_fields x).map
      regularCauchyRingEncodeBHist

def RegularCauchyRingTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option RegularCauchyRingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun eventFlow =>
    match eventFlow with
    | [A, B, WA, WB, DA, DB, S, G, M, L, RS, RG, RM, RL, ES, EG, EM, EL, H, C, P, N] =>
        some
          (RegularCauchyRingUp.mk
            (regularCauchyRingDecodeBHist A)
            (regularCauchyRingDecodeBHist B)
            (regularCauchyRingDecodeBHist WA)
            (regularCauchyRingDecodeBHist WB)
            (regularCauchyRingDecodeBHist DA)
            (regularCauchyRingDecodeBHist DB)
            (regularCauchyRingDecodeBHist S)
            (regularCauchyRingDecodeBHist G)
            (regularCauchyRingDecodeBHist M)
            (regularCauchyRingDecodeBHist L)
            (regularCauchyRingDecodeBHist RS)
            (regularCauchyRingDecodeBHist RG)
            (regularCauchyRingDecodeBHist RM)
            (regularCauchyRingDecodeBHist RL)
            (regularCauchyRingDecodeBHist ES)
            (regularCauchyRingDecodeBHist EG)
            (regularCauchyRingDecodeBHist EM)
            (regularCauchyRingDecodeBHist EL)
            (regularCauchyRingDecodeBHist H)
            (regularCauchyRingDecodeBHist C)
            (regularCauchyRingDecodeBHist P)
            (regularCauchyRingDecodeBHist N))
    | _ => none

def RegularCauchyRingTasteGate_single_carrier_alignment_carrier :
    BHistCarrier RegularCauchyRingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := RegularCauchyRingTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := RegularCauchyRingTasteGate_single_carrier_alignment_fromEventFlow

instance RegularCauchyRingTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier RegularCauchyRingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  RegularCauchyRingTasteGate_single_carrier_alignment_carrier

private theorem RegularCauchyRingTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchyRingUp,
      RegularCauchyRingTasteGate_single_carrier_alignment_fromEventFlow
          (RegularCauchyRingTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk A B WA WB DA DB S G M L RS RG RM RL ES EG EM EL H C P N =>
      change
        some
            (RegularCauchyRingUp.mk
              (regularCauchyRingDecodeBHist (regularCauchyRingEncodeBHist A))
              (regularCauchyRingDecodeBHist (regularCauchyRingEncodeBHist B))
              (regularCauchyRingDecodeBHist (regularCauchyRingEncodeBHist WA))
              (regularCauchyRingDecodeBHist (regularCauchyRingEncodeBHist WB))
              (regularCauchyRingDecodeBHist (regularCauchyRingEncodeBHist DA))
              (regularCauchyRingDecodeBHist (regularCauchyRingEncodeBHist DB))
              (regularCauchyRingDecodeBHist (regularCauchyRingEncodeBHist S))
              (regularCauchyRingDecodeBHist (regularCauchyRingEncodeBHist G))
              (regularCauchyRingDecodeBHist (regularCauchyRingEncodeBHist M))
              (regularCauchyRingDecodeBHist (regularCauchyRingEncodeBHist L))
              (regularCauchyRingDecodeBHist (regularCauchyRingEncodeBHist RS))
              (regularCauchyRingDecodeBHist (regularCauchyRingEncodeBHist RG))
              (regularCauchyRingDecodeBHist (regularCauchyRingEncodeBHist RM))
              (regularCauchyRingDecodeBHist (regularCauchyRingEncodeBHist RL))
              (regularCauchyRingDecodeBHist (regularCauchyRingEncodeBHist ES))
              (regularCauchyRingDecodeBHist (regularCauchyRingEncodeBHist EG))
              (regularCauchyRingDecodeBHist (regularCauchyRingEncodeBHist EM))
              (regularCauchyRingDecodeBHist (regularCauchyRingEncodeBHist EL))
              (regularCauchyRingDecodeBHist (regularCauchyRingEncodeBHist H))
              (regularCauchyRingDecodeBHist (regularCauchyRingEncodeBHist C))
              (regularCauchyRingDecodeBHist (regularCauchyRingEncodeBHist P))
              (regularCauchyRingDecodeBHist (regularCauchyRingEncodeBHist N))) =
          some (RegularCauchyRingUp.mk A B WA WB DA DB S G M L RS RG RM RL ES EG EM EL H C P N)
      rw [RegularCauchyRingTasteGate_single_carrier_alignment_decode_encode A]
      rw [RegularCauchyRingTasteGate_single_carrier_alignment_decode_encode B]
      rw [RegularCauchyRingTasteGate_single_carrier_alignment_decode_encode WA]
      rw [RegularCauchyRingTasteGate_single_carrier_alignment_decode_encode WB]
      rw [RegularCauchyRingTasteGate_single_carrier_alignment_decode_encode DA]
      rw [RegularCauchyRingTasteGate_single_carrier_alignment_decode_encode DB]
      rw [RegularCauchyRingTasteGate_single_carrier_alignment_decode_encode S]
      rw [RegularCauchyRingTasteGate_single_carrier_alignment_decode_encode G]
      rw [RegularCauchyRingTasteGate_single_carrier_alignment_decode_encode M]
      rw [RegularCauchyRingTasteGate_single_carrier_alignment_decode_encode L]
      rw [RegularCauchyRingTasteGate_single_carrier_alignment_decode_encode RS]
      rw [RegularCauchyRingTasteGate_single_carrier_alignment_decode_encode RG]
      rw [RegularCauchyRingTasteGate_single_carrier_alignment_decode_encode RM]
      rw [RegularCauchyRingTasteGate_single_carrier_alignment_decode_encode RL]
      rw [RegularCauchyRingTasteGate_single_carrier_alignment_decode_encode ES]
      rw [RegularCauchyRingTasteGate_single_carrier_alignment_decode_encode EG]
      rw [RegularCauchyRingTasteGate_single_carrier_alignment_decode_encode EM]
      rw [RegularCauchyRingTasteGate_single_carrier_alignment_decode_encode EL]
      rw [RegularCauchyRingTasteGate_single_carrier_alignment_decode_encode H]
      rw [RegularCauchyRingTasteGate_single_carrier_alignment_decode_encode C]
      rw [RegularCauchyRingTasteGate_single_carrier_alignment_decode_encode P]
      rw [RegularCauchyRingTasteGate_single_carrier_alignment_decode_encode N]

private theorem RegularCauchyRingTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyRingUp} :
    RegularCauchyRingTasteGate_single_carrier_alignment_toEventFlow x =
        RegularCauchyRingTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          RegularCauchyRingTasteGate_single_carrier_alignment_fromEventFlow
              (RegularCauchyRingTasteGate_single_carrier_alignment_toEventFlow x) :=
        (RegularCauchyRingTasteGate_single_carrier_alignment_round_trip x).symm
      _ =
          RegularCauchyRingTasteGate_single_carrier_alignment_fromEventFlow
              (RegularCauchyRingTasteGate_single_carrier_alignment_toEventFlow y) :=
        congrArg RegularCauchyRingTasteGate_single_carrier_alignment_fromEventFlow hxy
      _ = some y := RegularCauchyRingTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

private theorem RegularCauchyRingTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : RegularCauchyRingUp,
      RegularCauchyRingTasteGate_single_carrier_alignment_fields x =
          RegularCauchyRingTasteGate_single_carrier_alignment_fields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk A₁ B₁ WA₁ WB₁ DA₁ DB₁ S₁ G₁ M₁ L₁ RS₁ RG₁ RM₁ RL₁ ES₁ EG₁ EM₁ EL₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk A₂ B₂ WA₂ WB₂ DA₂ DB₂ S₂ G₂ M₂ L₂ RS₂ RG₂ RM₂ RL₂ ES₂ EG₂ EM₂ EL₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

def RegularCauchyRingTasteGate_single_carrier_alignment_gate :
    @ChapterTasteGate RegularCauchyRingUp
      RegularCauchyRingTasteGate_single_carrier_alignment_carrier where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    exact RegularCauchyRingTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RegularCauchyRingTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance RegularCauchyRingTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate RegularCauchyRingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  RegularCauchyRingTasteGate_single_carrier_alignment_gate

instance RegularCauchyRingTasteGate_single_carrier_alignment_FieldFaithful :
    FieldFaithful RegularCauchyRingUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := RegularCauchyRingTasteGate_single_carrier_alignment_fields
  field_faithful := RegularCauchyRingTasteGate_single_carrier_alignment_field_faithful

theorem RegularCauchyRingTasteGate_single_carrier_alignment :
    (forall h : BHist, regularCauchyRingDecodeBHist (regularCauchyRingEncodeBHist h) = h) ∧
      RegularCauchyRingTasteGate_single_carrier_alignment_fields
          (RegularCauchyRingUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] ∧
          regularCauchyRingEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨RegularCauchyRingTasteGate_single_carrier_alignment_decode_encode,
      ⟨rfl, rfl⟩⟩

end BEDC.Derived.RegularCauchyRingUp
