import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HahnDecompositionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HahnDecompositionUp : Type where
  | mk (S A B Z M R L E H C P N : BHist) : HahnDecompositionUp
  deriving DecidableEq

def hahnDecompositionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hahnDecompositionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hahnDecompositionEncodeBHist h

def hahnDecompositionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hahnDecompositionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hahnDecompositionDecodeBHist tail)

private theorem hahnDecompositionDecode_encode_bhist :
    ∀ h : BHist, hahnDecompositionDecodeBHist (hahnDecompositionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def hahnDecompositionFields : HahnDecompositionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HahnDecompositionUp.mk S A B Z M R L E H C P N => [S, A, B, Z, M, R, L, E, H, C, P, N]

def hahnDecompositionToEventFlow : HahnDecompositionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (hahnDecompositionFields x).map hahnDecompositionEncodeBHist

private def hahnDecompositionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => hahnDecompositionEventAtDefault index rest

def hahnDecompositionFromEventFlow (ef : EventFlow) : Option HahnDecompositionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HahnDecompositionUp.mk
      (hahnDecompositionDecodeBHist (hahnDecompositionEventAtDefault 0 ef))
      (hahnDecompositionDecodeBHist (hahnDecompositionEventAtDefault 1 ef))
      (hahnDecompositionDecodeBHist (hahnDecompositionEventAtDefault 2 ef))
      (hahnDecompositionDecodeBHist (hahnDecompositionEventAtDefault 3 ef))
      (hahnDecompositionDecodeBHist (hahnDecompositionEventAtDefault 4 ef))
      (hahnDecompositionDecodeBHist (hahnDecompositionEventAtDefault 5 ef))
      (hahnDecompositionDecodeBHist (hahnDecompositionEventAtDefault 6 ef))
      (hahnDecompositionDecodeBHist (hahnDecompositionEventAtDefault 7 ef))
      (hahnDecompositionDecodeBHist (hahnDecompositionEventAtDefault 8 ef))
      (hahnDecompositionDecodeBHist (hahnDecompositionEventAtDefault 9 ef))
      (hahnDecompositionDecodeBHist (hahnDecompositionEventAtDefault 10 ef))
      (hahnDecompositionDecodeBHist (hahnDecompositionEventAtDefault 11 ef)))

private theorem hahnDecomposition_round_trip :
    ∀ x : HahnDecompositionUp,
      hahnDecompositionFromEventFlow (hahnDecompositionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S A B Z M R L E H C P N =>
      change
        some
          (HahnDecompositionUp.mk
            (hahnDecompositionDecodeBHist (hahnDecompositionEncodeBHist S))
            (hahnDecompositionDecodeBHist (hahnDecompositionEncodeBHist A))
            (hahnDecompositionDecodeBHist (hahnDecompositionEncodeBHist B))
            (hahnDecompositionDecodeBHist (hahnDecompositionEncodeBHist Z))
            (hahnDecompositionDecodeBHist (hahnDecompositionEncodeBHist M))
            (hahnDecompositionDecodeBHist (hahnDecompositionEncodeBHist R))
            (hahnDecompositionDecodeBHist (hahnDecompositionEncodeBHist L))
            (hahnDecompositionDecodeBHist (hahnDecompositionEncodeBHist E))
            (hahnDecompositionDecodeBHist (hahnDecompositionEncodeBHist H))
            (hahnDecompositionDecodeBHist (hahnDecompositionEncodeBHist C))
            (hahnDecompositionDecodeBHist (hahnDecompositionEncodeBHist P))
            (hahnDecompositionDecodeBHist (hahnDecompositionEncodeBHist N))) =
          some (HahnDecompositionUp.mk S A B Z M R L E H C P N)
      rw [hahnDecompositionDecode_encode_bhist S, hahnDecompositionDecode_encode_bhist A,
        hahnDecompositionDecode_encode_bhist B, hahnDecompositionDecode_encode_bhist Z,
        hahnDecompositionDecode_encode_bhist M, hahnDecompositionDecode_encode_bhist R,
        hahnDecompositionDecode_encode_bhist L, hahnDecompositionDecode_encode_bhist E,
        hahnDecompositionDecode_encode_bhist H, hahnDecompositionDecode_encode_bhist C,
        hahnDecompositionDecode_encode_bhist P, hahnDecompositionDecode_encode_bhist N]

private theorem hahnDecompositionToEventFlow_injective {x y : HahnDecompositionUp} :
    hahnDecompositionToEventFlow x = hahnDecompositionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hahnDecompositionFromEventFlow (hahnDecompositionToEventFlow x) =
        hahnDecompositionFromEventFlow (hahnDecompositionToEventFlow y) :=
    congrArg hahnDecompositionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (hahnDecomposition_round_trip x).symm
      (Eq.trans hread (hahnDecomposition_round_trip y)))

private theorem hahnDecomposition_fields_faithful :
    ∀ x y : HahnDecompositionUp, hahnDecompositionFields x = hahnDecompositionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 A1 B1 Z1 M1 R1 L1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 A2 B2 Z2 M2 R2 L2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance hahnDecompositionBHistCarrier : BHistCarrier HahnDecompositionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hahnDecompositionToEventFlow
  fromEventFlow := hahnDecompositionFromEventFlow

instance hahnDecompositionChapterTasteGate : ChapterTasteGate HahnDecompositionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change hahnDecompositionFromEventFlow (hahnDecompositionToEventFlow x) = some x
    exact hahnDecomposition_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (hahnDecompositionToEventFlow_injective heq)

instance hahnDecompositionFieldFaithful : FieldFaithful HahnDecompositionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := hahnDecompositionFields
  field_faithful := hahnDecomposition_fields_faithful

instance hahnDecompositionNontrivial : BEDC.Meta.TasteGate.Nontrivial HahnDecompositionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨HahnDecompositionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      HahnDecompositionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

theorem HahnDecompositionTasteGate_single_carrier_alignment :
    (∀ h : BHist, hahnDecompositionDecodeBHist (hahnDecompositionEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier HahnDecompositionUp) ∧
        Nonempty (ChapterTasteGate HahnDecompositionUp) ∧
          Nonempty (FieldFaithful HahnDecompositionUp) ∧
            Nonempty (BEDC.Meta.TasteGate.Nontrivial HahnDecompositionUp) ∧
              hahnDecompositionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨hahnDecompositionDecode_encode_bhist,
      ⟨hahnDecompositionBHistCarrier⟩,
      ⟨hahnDecompositionChapterTasteGate⟩,
      ⟨hahnDecompositionFieldFaithful⟩,
      ⟨hahnDecompositionNontrivial⟩,
      rfl⟩

end BEDC.Derived.HahnDecompositionUp
