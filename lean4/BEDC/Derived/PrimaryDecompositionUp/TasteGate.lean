import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PrimaryDecompositionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PrimaryDecompositionUp : Type where
  | mk (R M I B G L E H C Q N : BHist) : PrimaryDecompositionUp
  deriving DecidableEq

private def primaryDecompositionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: primaryDecompositionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: primaryDecompositionEncodeBHist h

private def primaryDecompositionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (primaryDecompositionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (primaryDecompositionDecodeBHist tail)

private theorem PrimaryDecompositionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, primaryDecompositionDecodeBHist (primaryDecompositionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def primaryDecompositionFields : PrimaryDecompositionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PrimaryDecompositionUp.mk R M I B G L E H C Q N => [R, M, I, B, G, L, E, H, C, Q, N]

private def primaryDecompositionToEventFlow : PrimaryDecompositionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (primaryDecompositionFields x).map primaryDecompositionEncodeBHist

private def primaryDecompositionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => primaryDecompositionEventAtDefault index rest

private def primaryDecompositionFromEventFlow (ef : EventFlow) :
    Option PrimaryDecompositionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (PrimaryDecompositionUp.mk
      (primaryDecompositionDecodeBHist (primaryDecompositionEventAtDefault 0 ef))
      (primaryDecompositionDecodeBHist (primaryDecompositionEventAtDefault 1 ef))
      (primaryDecompositionDecodeBHist (primaryDecompositionEventAtDefault 2 ef))
      (primaryDecompositionDecodeBHist (primaryDecompositionEventAtDefault 3 ef))
      (primaryDecompositionDecodeBHist (primaryDecompositionEventAtDefault 4 ef))
      (primaryDecompositionDecodeBHist (primaryDecompositionEventAtDefault 5 ef))
      (primaryDecompositionDecodeBHist (primaryDecompositionEventAtDefault 6 ef))
      (primaryDecompositionDecodeBHist (primaryDecompositionEventAtDefault 7 ef))
      (primaryDecompositionDecodeBHist (primaryDecompositionEventAtDefault 8 ef))
      (primaryDecompositionDecodeBHist (primaryDecompositionEventAtDefault 9 ef))
      (primaryDecompositionDecodeBHist (primaryDecompositionEventAtDefault 10 ef)))

private theorem PrimaryDecompositionTasteGate_single_carrier_alignment_round_trip
    (x : PrimaryDecompositionUp) :
    primaryDecompositionFromEventFlow (primaryDecompositionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk R M I B G L E H C Q N =>
      change
        some
          (PrimaryDecompositionUp.mk
            (primaryDecompositionDecodeBHist (primaryDecompositionEncodeBHist R))
            (primaryDecompositionDecodeBHist (primaryDecompositionEncodeBHist M))
            (primaryDecompositionDecodeBHist (primaryDecompositionEncodeBHist I))
            (primaryDecompositionDecodeBHist (primaryDecompositionEncodeBHist B))
            (primaryDecompositionDecodeBHist (primaryDecompositionEncodeBHist G))
            (primaryDecompositionDecodeBHist (primaryDecompositionEncodeBHist L))
            (primaryDecompositionDecodeBHist (primaryDecompositionEncodeBHist E))
            (primaryDecompositionDecodeBHist (primaryDecompositionEncodeBHist H))
            (primaryDecompositionDecodeBHist (primaryDecompositionEncodeBHist C))
            (primaryDecompositionDecodeBHist (primaryDecompositionEncodeBHist Q))
            (primaryDecompositionDecodeBHist (primaryDecompositionEncodeBHist N))) =
          some (PrimaryDecompositionUp.mk R M I B G L E H C Q N)
      rw [PrimaryDecompositionTasteGate_single_carrier_alignment_decode_encode R,
        PrimaryDecompositionTasteGate_single_carrier_alignment_decode_encode M,
        PrimaryDecompositionTasteGate_single_carrier_alignment_decode_encode I,
        PrimaryDecompositionTasteGate_single_carrier_alignment_decode_encode B,
        PrimaryDecompositionTasteGate_single_carrier_alignment_decode_encode G,
        PrimaryDecompositionTasteGate_single_carrier_alignment_decode_encode L,
        PrimaryDecompositionTasteGate_single_carrier_alignment_decode_encode E,
        PrimaryDecompositionTasteGate_single_carrier_alignment_decode_encode H,
        PrimaryDecompositionTasteGate_single_carrier_alignment_decode_encode C,
        PrimaryDecompositionTasteGate_single_carrier_alignment_decode_encode Q,
        PrimaryDecompositionTasteGate_single_carrier_alignment_decode_encode N]

private theorem PrimaryDecompositionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : PrimaryDecompositionUp} :
    primaryDecompositionToEventFlow x = primaryDecompositionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      primaryDecompositionFromEventFlow (primaryDecompositionToEventFlow x) =
        primaryDecompositionFromEventFlow (primaryDecompositionToEventFlow y) :=
    congrArg primaryDecompositionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (PrimaryDecompositionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (PrimaryDecompositionTasteGate_single_carrier_alignment_round_trip y)))

private theorem PrimaryDecompositionTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : PrimaryDecompositionUp,
      primaryDecompositionFields x = primaryDecompositionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R1 M1 I1 B1 G1 L1 E1 H1 C1 Q1 N1 =>
      cases y with
      | mk R2 M2 I2 B2 G2 L2 E2 H2 C2 Q2 N2 =>
          cases hfields
          rfl

instance primaryDecompositionBHistCarrier : BHistCarrier PrimaryDecompositionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := primaryDecompositionToEventFlow
  fromEventFlow := primaryDecompositionFromEventFlow

instance primaryDecompositionChapterTasteGate :
    ChapterTasteGate PrimaryDecompositionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change primaryDecompositionFromEventFlow (primaryDecompositionToEventFlow x) = some x
    exact PrimaryDecompositionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (PrimaryDecompositionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate PrimaryDecompositionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  primaryDecompositionChapterTasteGate

instance primaryDecompositionFieldFaithful :
    FieldFaithful PrimaryDecompositionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := primaryDecompositionFields
  field_faithful := PrimaryDecompositionTasteGate_single_carrier_alignment_field_faithful

instance primaryDecompositionNontrivial : Nontrivial PrimaryDecompositionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PrimaryDecompositionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      PrimaryDecompositionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem PrimaryDecompositionTasteGate_single_carrier_alignment :
    (∀ h : BHist, primaryDecompositionDecodeBHist (primaryDecompositionEncodeBHist h) = h) ∧
      (∀ x : PrimaryDecompositionUp,
        primaryDecompositionFromEventFlow (primaryDecompositionToEventFlow x) = some x) ∧
        (∀ x y : PrimaryDecompositionUp,
          primaryDecompositionToEventFlow x = primaryDecompositionToEventFlow y → x = y) ∧
          primaryDecompositionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨PrimaryDecompositionTasteGate_single_carrier_alignment_decode_encode,
      PrimaryDecompositionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => PrimaryDecompositionTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.PrimaryDecompositionUp
