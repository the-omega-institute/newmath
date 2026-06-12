import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HausdorffUniformityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HausdorffUniformityUp : Type where
  | mk (U E D Z T C P N : BHist) : HausdorffUniformityUp
  deriving DecidableEq

def hausdorffUniformityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hausdorffUniformityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hausdorffUniformityEncodeBHist h

def hausdorffUniformityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hausdorffUniformityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hausdorffUniformityDecodeBHist tail)

private theorem hausdorffUniformity_decode_encode_bhist :
    ∀ h : BHist,
      hausdorffUniformityDecodeBHist (hausdorffUniformityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def hausdorffUniformityFields : HausdorffUniformityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HausdorffUniformityUp.mk U E D Z T C P N => [U, E, D, Z, T, C, P, N]

def hausdorffUniformityToEventFlow : HausdorffUniformityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (hausdorffUniformityFields x).map hausdorffUniformityEncodeBHist

private def hausdorffUniformityEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => hausdorffUniformityEventAt index rest

def hausdorffUniformityFromEventFlow : EventFlow → Option HausdorffUniformityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun flow =>
    some
      (HausdorffUniformityUp.mk
        (hausdorffUniformityDecodeBHist (hausdorffUniformityEventAt 0 flow))
        (hausdorffUniformityDecodeBHist (hausdorffUniformityEventAt 1 flow))
        (hausdorffUniformityDecodeBHist (hausdorffUniformityEventAt 2 flow))
        (hausdorffUniformityDecodeBHist (hausdorffUniformityEventAt 3 flow))
        (hausdorffUniformityDecodeBHist (hausdorffUniformityEventAt 4 flow))
        (hausdorffUniformityDecodeBHist (hausdorffUniformityEventAt 5 flow))
        (hausdorffUniformityDecodeBHist (hausdorffUniformityEventAt 6 flow))
        (hausdorffUniformityDecodeBHist (hausdorffUniformityEventAt 7 flow)))

private theorem hausdorffUniformity_round_trip :
    ∀ x : HausdorffUniformityUp,
      hausdorffUniformityFromEventFlow (hausdorffUniformityToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk U E D Z T C P N =>
      change
        some
            (HausdorffUniformityUp.mk
              (hausdorffUniformityDecodeBHist (hausdorffUniformityEncodeBHist U))
              (hausdorffUniformityDecodeBHist (hausdorffUniformityEncodeBHist E))
              (hausdorffUniformityDecodeBHist (hausdorffUniformityEncodeBHist D))
              (hausdorffUniformityDecodeBHist (hausdorffUniformityEncodeBHist Z))
              (hausdorffUniformityDecodeBHist (hausdorffUniformityEncodeBHist T))
              (hausdorffUniformityDecodeBHist (hausdorffUniformityEncodeBHist C))
              (hausdorffUniformityDecodeBHist (hausdorffUniformityEncodeBHist P))
              (hausdorffUniformityDecodeBHist (hausdorffUniformityEncodeBHist N))) =
          some (HausdorffUniformityUp.mk U E D Z T C P N)
      rw [hausdorffUniformity_decode_encode_bhist U,
        hausdorffUniformity_decode_encode_bhist E,
        hausdorffUniformity_decode_encode_bhist D,
        hausdorffUniformity_decode_encode_bhist Z,
        hausdorffUniformity_decode_encode_bhist T,
        hausdorffUniformity_decode_encode_bhist C,
        hausdorffUniformity_decode_encode_bhist P,
        hausdorffUniformity_decode_encode_bhist N]

private theorem hausdorffUniformityToEventFlow_injective
    {x y : HausdorffUniformityUp} :
    hausdorffUniformityToEventFlow x = hausdorffUniformityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have hread :
      hausdorffUniformityFromEventFlow (hausdorffUniformityToEventFlow x) =
        hausdorffUniformityFromEventFlow (hausdorffUniformityToEventFlow y) :=
    congrArg hausdorffUniformityFromEventFlow hxy
  exact Option.some.inj
    (Eq.trans (hausdorffUniformity_round_trip x).symm
      (Eq.trans hread (hausdorffUniformity_round_trip y)))

private theorem hausdorffUniformity_field_faithful :
    ∀ x y : HausdorffUniformityUp,
      hausdorffUniformityFields x = hausdorffUniformityFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk U1 E1 D1 Z1 T1 C1 P1 N1 =>
      cases y with
      | mk U2 E2 D2 Z2 T2 C2 P2 N2 =>
          injection hfields with hU tail0
          injection tail0 with hE tail1
          injection tail1 with hD tail2
          injection tail2 with hZ tail3
          injection tail3 with hT tail4
          injection tail4 with hC tail5
          injection tail5 with hP tail6
          injection tail6 with hN _
          subst hU
          subst hE
          subst hD
          subst hZ
          subst hT
          subst hC
          subst hP
          subst hN
          rfl

instance hausdorffUniformityBHistCarrier : BHistCarrier HausdorffUniformityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hausdorffUniformityToEventFlow
  fromEventFlow := hausdorffUniformityFromEventFlow

instance hausdorffUniformityChapterTasteGate :
    ChapterTasteGate HausdorffUniformityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      hausdorffUniformityFromEventFlow (hausdorffUniformityToEventFlow x) =
        some x
    exact hausdorffUniformity_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (hausdorffUniformityToEventFlow_injective heq)

instance hausdorffUniformityFieldFaithful : FieldFaithful HausdorffUniformityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := hausdorffUniformityFields
  field_faithful := hausdorffUniformity_field_faithful

instance hausdorffUniformityNontrivial : Nontrivial HausdorffUniformityUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨HausdorffUniformityUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      HausdorffUniformityUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate HausdorffUniformityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  hausdorffUniformityChapterTasteGate

theorem HausdorffUniformityTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      hausdorffUniformityDecodeBHist (hausdorffUniformityEncodeBHist h) = h) ∧
      (∀ x : HausdorffUniformityUp,
        hausdorffUniformityFromEventFlow (hausdorffUniformityToEventFlow x) =
          some x) ∧
        (∀ x y : HausdorffUniformityUp,
          hausdorffUniformityToEventFlow x = hausdorffUniformityToEventFlow y →
            x = y) ∧
          Nonempty (ChapterTasteGate HausdorffUniformityUp) ∧
            Nonempty (FieldFaithful HausdorffUniformityUp) ∧
              Nonempty (Nontrivial HausdorffUniformityUp) ∧
                hausdorffUniformityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨hausdorffUniformity_decode_encode_bhist,
      hausdorffUniformity_round_trip,
      fun _ _ hxy => hausdorffUniformityToEventFlow_injective hxy,
      ⟨hausdorffUniformityChapterTasteGate⟩,
      ⟨hausdorffUniformityFieldFaithful⟩,
      ⟨hausdorffUniformityNontrivial⟩,
      rfl⟩

end BEDC.Derived.HausdorffUniformityUp
