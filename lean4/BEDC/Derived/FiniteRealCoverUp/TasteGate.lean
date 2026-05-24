import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteRealCoverUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteRealCoverUp : Type where
  | mk (M R D B W E H C P N : BHist) : FiniteRealCoverUp
  deriving DecidableEq

def finiteRealCoverEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteRealCoverEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteRealCoverEncodeBHist h

def finiteRealCoverDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteRealCoverDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteRealCoverDecodeBHist tail)

private theorem FiniteRealCoverTasteGate_single_carrier_alignment_decode :
    forall h : BHist, finiteRealCoverDecodeBHist (finiteRealCoverEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteRealCoverToEventFlow : FiniteRealCoverUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteRealCoverUp.mk M R D B W E H C P N =>
      [finiteRealCoverEncodeBHist M,
        finiteRealCoverEncodeBHist R,
        finiteRealCoverEncodeBHist D,
        finiteRealCoverEncodeBHist B,
        finiteRealCoverEncodeBHist W,
        finiteRealCoverEncodeBHist E,
        finiteRealCoverEncodeBHist H,
        finiteRealCoverEncodeBHist C,
        finiteRealCoverEncodeBHist P,
        finiteRealCoverEncodeBHist N]

private def finiteRealCoverEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => finiteRealCoverEventAtDefault index rest

def finiteRealCoverFromEventFlow (ef : EventFlow) : Option FiniteRealCoverUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FiniteRealCoverUp.mk
      (finiteRealCoverDecodeBHist (finiteRealCoverEventAtDefault 0 ef))
      (finiteRealCoverDecodeBHist (finiteRealCoverEventAtDefault 1 ef))
      (finiteRealCoverDecodeBHist (finiteRealCoverEventAtDefault 2 ef))
      (finiteRealCoverDecodeBHist (finiteRealCoverEventAtDefault 3 ef))
      (finiteRealCoverDecodeBHist (finiteRealCoverEventAtDefault 4 ef))
      (finiteRealCoverDecodeBHist (finiteRealCoverEventAtDefault 5 ef))
      (finiteRealCoverDecodeBHist (finiteRealCoverEventAtDefault 6 ef))
      (finiteRealCoverDecodeBHist (finiteRealCoverEventAtDefault 7 ef))
      (finiteRealCoverDecodeBHist (finiteRealCoverEventAtDefault 8 ef))
      (finiteRealCoverDecodeBHist (finiteRealCoverEventAtDefault 9 ef)))

private theorem FiniteRealCoverTasteGate_single_carrier_alignment_round_trip :
    forall x : FiniteRealCoverUp,
      finiteRealCoverFromEventFlow (finiteRealCoverToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M R D B W E H C P N =>
      change
        some
          (FiniteRealCoverUp.mk
            (finiteRealCoverDecodeBHist (finiteRealCoverEncodeBHist M))
            (finiteRealCoverDecodeBHist (finiteRealCoverEncodeBHist R))
            (finiteRealCoverDecodeBHist (finiteRealCoverEncodeBHist D))
            (finiteRealCoverDecodeBHist (finiteRealCoverEncodeBHist B))
            (finiteRealCoverDecodeBHist (finiteRealCoverEncodeBHist W))
            (finiteRealCoverDecodeBHist (finiteRealCoverEncodeBHist E))
            (finiteRealCoverDecodeBHist (finiteRealCoverEncodeBHist H))
            (finiteRealCoverDecodeBHist (finiteRealCoverEncodeBHist C))
            (finiteRealCoverDecodeBHist (finiteRealCoverEncodeBHist P))
            (finiteRealCoverDecodeBHist (finiteRealCoverEncodeBHist N))) =
          some (FiniteRealCoverUp.mk M R D B W E H C P N)
      rw [FiniteRealCoverTasteGate_single_carrier_alignment_decode M,
        FiniteRealCoverTasteGate_single_carrier_alignment_decode R,
        FiniteRealCoverTasteGate_single_carrier_alignment_decode D,
        FiniteRealCoverTasteGate_single_carrier_alignment_decode B,
        FiniteRealCoverTasteGate_single_carrier_alignment_decode W,
        FiniteRealCoverTasteGate_single_carrier_alignment_decode E,
        FiniteRealCoverTasteGate_single_carrier_alignment_decode H,
        FiniteRealCoverTasteGate_single_carrier_alignment_decode C,
        FiniteRealCoverTasteGate_single_carrier_alignment_decode P,
        FiniteRealCoverTasteGate_single_carrier_alignment_decode N]

private theorem FiniteRealCoverTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FiniteRealCoverUp} :
    finiteRealCoverToEventFlow x = finiteRealCoverToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteRealCoverFromEventFlow (finiteRealCoverToEventFlow x) =
        finiteRealCoverFromEventFlow (finiteRealCoverToEventFlow y) :=
    congrArg finiteRealCoverFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (FiniteRealCoverTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (FiniteRealCoverTasteGate_single_carrier_alignment_round_trip y)))

private def finiteRealCoverFields : FiniteRealCoverUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteRealCoverUp.mk M R D B W E H C P N => [M, R, D, B, W, E, H, C, P, N]

private theorem FiniteRealCoverTasteGate_single_carrier_alignment_fields :
    forall x y : FiniteRealCoverUp,
      finiteRealCoverFields x = finiteRealCoverFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M1 R1 D1 B1 W1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk M2 R2 D2 B2 W2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance finiteRealCoverBHistCarrier : BHistCarrier FiniteRealCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteRealCoverToEventFlow
  fromEventFlow := finiteRealCoverFromEventFlow

instance finiteRealCoverChapterTasteGate : ChapterTasteGate FiniteRealCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteRealCoverFromEventFlow (finiteRealCoverToEventFlow x) = some x
    exact FiniteRealCoverTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FiniteRealCoverTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance finiteRealCoverFieldFaithful : FieldFaithful FiniteRealCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteRealCoverFields
  field_faithful := FiniteRealCoverTasteGate_single_carrier_alignment_fields

def taste_gate : ChapterTasteGate FiniteRealCoverUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteRealCoverChapterTasteGate

theorem FiniteRealCoverTasteGate_single_carrier_alignment :
    (forall h : BHist, finiteRealCoverDecodeBHist (finiteRealCoverEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier FiniteRealCoverUp) ∧
        Nonempty (ChapterTasteGate FiniteRealCoverUp) ∧
          Nonempty (FieldFaithful FiniteRealCoverUp) ∧
            finiteRealCoverEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  exact
    ⟨FiniteRealCoverTasteGate_single_carrier_alignment_decode,
      ⟨finiteRealCoverBHistCarrier⟩,
      ⟨finiteRealCoverChapterTasteGate⟩,
      ⟨finiteRealCoverFieldFaithful⟩,
      rfl⟩

end BEDC.Derived.FiniteRealCoverUp
