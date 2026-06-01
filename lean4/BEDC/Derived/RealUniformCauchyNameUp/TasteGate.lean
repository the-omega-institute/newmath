import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealUniformCauchyNameUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealUniformCauchyNameUp : Type where
  | mk (S R M Q D E H C P N : BHist) : RealUniformCauchyNameUp
  deriving DecidableEq

def realUniformCauchyNameEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realUniformCauchyNameEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realUniformCauchyNameEncodeBHist h

def realUniformCauchyNameDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realUniformCauchyNameDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realUniformCauchyNameDecodeBHist tail)

private theorem RealUniformCauchyNameTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      realUniformCauchyNameDecodeBHist (realUniformCauchyNameEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realUniformCauchyNameFields : RealUniformCauchyNameUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealUniformCauchyNameUp.mk S R M Q D E H C P N => [S, R, M, Q, D, E, H, C, P, N]

def realUniformCauchyNameToEventFlow : RealUniformCauchyNameUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (realUniformCauchyNameFields x).map realUniformCauchyNameEncodeBHist

private def realUniformCauchyNameEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realUniformCauchyNameEventAtDefault index rest

def realUniformCauchyNameFromEventFlow
    (ef : EventFlow) : Option RealUniformCauchyNameUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealUniformCauchyNameUp.mk
      (realUniformCauchyNameDecodeBHist (realUniformCauchyNameEventAtDefault 0 ef))
      (realUniformCauchyNameDecodeBHist (realUniformCauchyNameEventAtDefault 1 ef))
      (realUniformCauchyNameDecodeBHist (realUniformCauchyNameEventAtDefault 2 ef))
      (realUniformCauchyNameDecodeBHist (realUniformCauchyNameEventAtDefault 3 ef))
      (realUniformCauchyNameDecodeBHist (realUniformCauchyNameEventAtDefault 4 ef))
      (realUniformCauchyNameDecodeBHist (realUniformCauchyNameEventAtDefault 5 ef))
      (realUniformCauchyNameDecodeBHist (realUniformCauchyNameEventAtDefault 6 ef))
      (realUniformCauchyNameDecodeBHist (realUniformCauchyNameEventAtDefault 7 ef))
      (realUniformCauchyNameDecodeBHist (realUniformCauchyNameEventAtDefault 8 ef))
      (realUniformCauchyNameDecodeBHist (realUniformCauchyNameEventAtDefault 9 ef)))

private theorem RealUniformCauchyNameTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RealUniformCauchyNameUp,
      realUniformCauchyNameFromEventFlow (realUniformCauchyNameToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk S R M Q D E H C P N =>
      change
        some
          (RealUniformCauchyNameUp.mk
            (realUniformCauchyNameDecodeBHist (realUniformCauchyNameEncodeBHist S))
            (realUniformCauchyNameDecodeBHist (realUniformCauchyNameEncodeBHist R))
            (realUniformCauchyNameDecodeBHist (realUniformCauchyNameEncodeBHist M))
            (realUniformCauchyNameDecodeBHist (realUniformCauchyNameEncodeBHist Q))
            (realUniformCauchyNameDecodeBHist (realUniformCauchyNameEncodeBHist D))
            (realUniformCauchyNameDecodeBHist (realUniformCauchyNameEncodeBHist E))
            (realUniformCauchyNameDecodeBHist (realUniformCauchyNameEncodeBHist H))
            (realUniformCauchyNameDecodeBHist (realUniformCauchyNameEncodeBHist C))
            (realUniformCauchyNameDecodeBHist (realUniformCauchyNameEncodeBHist P))
            (realUniformCauchyNameDecodeBHist (realUniformCauchyNameEncodeBHist N))) =
          some (RealUniformCauchyNameUp.mk S R M Q D E H C P N)
      rw [RealUniformCauchyNameTasteGate_single_carrier_alignment_decode S,
        RealUniformCauchyNameTasteGate_single_carrier_alignment_decode R,
        RealUniformCauchyNameTasteGate_single_carrier_alignment_decode M,
        RealUniformCauchyNameTasteGate_single_carrier_alignment_decode Q,
        RealUniformCauchyNameTasteGate_single_carrier_alignment_decode D,
        RealUniformCauchyNameTasteGate_single_carrier_alignment_decode E,
        RealUniformCauchyNameTasteGate_single_carrier_alignment_decode H,
        RealUniformCauchyNameTasteGate_single_carrier_alignment_decode C,
        RealUniformCauchyNameTasteGate_single_carrier_alignment_decode P,
        RealUniformCauchyNameTasteGate_single_carrier_alignment_decode N]

private theorem RealUniformCauchyNameTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RealUniformCauchyNameUp} :
    realUniformCauchyNameToEventFlow x = realUniformCauchyNameToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realUniformCauchyNameFromEventFlow (realUniformCauchyNameToEventFlow x) =
        realUniformCauchyNameFromEventFlow (realUniformCauchyNameToEventFlow y) :=
    congrArg realUniformCauchyNameFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RealUniformCauchyNameTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RealUniformCauchyNameTasteGate_single_carrier_alignment_round_trip y)))

private theorem RealUniformCauchyNameTasteGate_single_carrier_alignment_fields :
    ∀ x y : RealUniformCauchyNameUp,
      realUniformCauchyNameFields x = realUniformCauchyNameFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 R1 M1 Q1 D1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 R2 M2 Q2 D2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance realUniformCauchyNameBHistCarrier : BHistCarrier RealUniformCauchyNameUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realUniformCauchyNameToEventFlow
  fromEventFlow := realUniformCauchyNameFromEventFlow

instance realUniformCauchyNameChapterTasteGate :
    ChapterTasteGate RealUniformCauchyNameUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realUniformCauchyNameFromEventFlow (realUniformCauchyNameToEventFlow x) = some x
    exact RealUniformCauchyNameTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RealUniformCauchyNameTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance realUniformCauchyNameFieldFaithful : FieldFaithful RealUniformCauchyNameUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realUniformCauchyNameFields
  field_faithful := RealUniformCauchyNameTasteGate_single_carrier_alignment_fields

instance realUniformCauchyNameNontrivial : Nontrivial RealUniformCauchyNameUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealUniformCauchyNameUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealUniformCauchyNameUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealUniformCauchyNameUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realUniformCauchyNameChapterTasteGate

theorem RealUniformCauchyNameTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      realUniformCauchyNameDecodeBHist (realUniformCauchyNameEncodeBHist h) = h) ∧
      (∀ x : RealUniformCauchyNameUp,
        realUniformCauchyNameFromEventFlow
          (realUniformCauchyNameToEventFlow x) = some x) ∧
        (∀ x y : RealUniformCauchyNameUp,
          realUniformCauchyNameToEventFlow x =
            realUniformCauchyNameToEventFlow y → x = y) ∧
          realUniformCauchyNameEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨RealUniformCauchyNameTasteGate_single_carrier_alignment_decode,
      RealUniformCauchyNameTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        RealUniformCauchyNameTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RealUniformCauchyNameUp
