import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteSubcoverRadiusLedgerUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteSubcoverRadiusLedgerUp : Type where
  | mk (K F G R B U H C P N : BHist) : FiniteSubcoverRadiusLedgerUp
  deriving DecidableEq

def finiteSubcoverRadiusLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteSubcoverRadiusLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteSubcoverRadiusLedgerEncodeBHist h

def finiteSubcoverRadiusLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteSubcoverRadiusLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteSubcoverRadiusLedgerDecodeBHist tail)

private theorem FiniteSubcoverRadiusLedgerTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      finiteSubcoverRadiusLedgerDecodeBHist
        (finiteSubcoverRadiusLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteSubcoverRadiusLedgerToEventFlow : FiniteSubcoverRadiusLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteSubcoverRadiusLedgerUp.mk K F G R B U H C P N =>
      [finiteSubcoverRadiusLedgerEncodeBHist K,
        finiteSubcoverRadiusLedgerEncodeBHist F,
        finiteSubcoverRadiusLedgerEncodeBHist G,
        finiteSubcoverRadiusLedgerEncodeBHist R,
        finiteSubcoverRadiusLedgerEncodeBHist B,
        finiteSubcoverRadiusLedgerEncodeBHist U,
        finiteSubcoverRadiusLedgerEncodeBHist H,
        finiteSubcoverRadiusLedgerEncodeBHist C,
        finiteSubcoverRadiusLedgerEncodeBHist P,
        finiteSubcoverRadiusLedgerEncodeBHist N]

private def finiteSubcoverRadiusLedgerEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      finiteSubcoverRadiusLedgerEventAtDefault index rest

def finiteSubcoverRadiusLedgerFromEventFlow
    (ef : EventFlow) : Option FiniteSubcoverRadiusLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FiniteSubcoverRadiusLedgerUp.mk
      (finiteSubcoverRadiusLedgerDecodeBHist
        (finiteSubcoverRadiusLedgerEventAtDefault 0 ef))
      (finiteSubcoverRadiusLedgerDecodeBHist
        (finiteSubcoverRadiusLedgerEventAtDefault 1 ef))
      (finiteSubcoverRadiusLedgerDecodeBHist
        (finiteSubcoverRadiusLedgerEventAtDefault 2 ef))
      (finiteSubcoverRadiusLedgerDecodeBHist
        (finiteSubcoverRadiusLedgerEventAtDefault 3 ef))
      (finiteSubcoverRadiusLedgerDecodeBHist
        (finiteSubcoverRadiusLedgerEventAtDefault 4 ef))
      (finiteSubcoverRadiusLedgerDecodeBHist
        (finiteSubcoverRadiusLedgerEventAtDefault 5 ef))
      (finiteSubcoverRadiusLedgerDecodeBHist
        (finiteSubcoverRadiusLedgerEventAtDefault 6 ef))
      (finiteSubcoverRadiusLedgerDecodeBHist
        (finiteSubcoverRadiusLedgerEventAtDefault 7 ef))
      (finiteSubcoverRadiusLedgerDecodeBHist
        (finiteSubcoverRadiusLedgerEventAtDefault 8 ef))
      (finiteSubcoverRadiusLedgerDecodeBHist
        (finiteSubcoverRadiusLedgerEventAtDefault 9 ef)))

private theorem FiniteSubcoverRadiusLedgerTasteGate_single_carrier_alignment_round_trip :
    ∀ x : FiniteSubcoverRadiusLedgerUp,
      finiteSubcoverRadiusLedgerFromEventFlow (finiteSubcoverRadiusLedgerToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K F G R B U H C P N =>
      change
        some
            (FiniteSubcoverRadiusLedgerUp.mk
              (finiteSubcoverRadiusLedgerDecodeBHist
                (finiteSubcoverRadiusLedgerEncodeBHist K))
              (finiteSubcoverRadiusLedgerDecodeBHist
                (finiteSubcoverRadiusLedgerEncodeBHist F))
              (finiteSubcoverRadiusLedgerDecodeBHist
                (finiteSubcoverRadiusLedgerEncodeBHist G))
              (finiteSubcoverRadiusLedgerDecodeBHist
                (finiteSubcoverRadiusLedgerEncodeBHist R))
              (finiteSubcoverRadiusLedgerDecodeBHist
                (finiteSubcoverRadiusLedgerEncodeBHist B))
              (finiteSubcoverRadiusLedgerDecodeBHist
                (finiteSubcoverRadiusLedgerEncodeBHist U))
              (finiteSubcoverRadiusLedgerDecodeBHist
                (finiteSubcoverRadiusLedgerEncodeBHist H))
              (finiteSubcoverRadiusLedgerDecodeBHist
                (finiteSubcoverRadiusLedgerEncodeBHist C))
              (finiteSubcoverRadiusLedgerDecodeBHist
                (finiteSubcoverRadiusLedgerEncodeBHist P))
              (finiteSubcoverRadiusLedgerDecodeBHist
                (finiteSubcoverRadiusLedgerEncodeBHist N))) =
          some (FiniteSubcoverRadiusLedgerUp.mk K F G R B U H C P N)
      rw [FiniteSubcoverRadiusLedgerTasteGate_single_carrier_alignment_decode K,
        FiniteSubcoverRadiusLedgerTasteGate_single_carrier_alignment_decode F,
        FiniteSubcoverRadiusLedgerTasteGate_single_carrier_alignment_decode G,
        FiniteSubcoverRadiusLedgerTasteGate_single_carrier_alignment_decode R,
        FiniteSubcoverRadiusLedgerTasteGate_single_carrier_alignment_decode B,
        FiniteSubcoverRadiusLedgerTasteGate_single_carrier_alignment_decode U,
        FiniteSubcoverRadiusLedgerTasteGate_single_carrier_alignment_decode H,
        FiniteSubcoverRadiusLedgerTasteGate_single_carrier_alignment_decode C,
        FiniteSubcoverRadiusLedgerTasteGate_single_carrier_alignment_decode P,
        FiniteSubcoverRadiusLedgerTasteGate_single_carrier_alignment_decode N]

private theorem FiniteSubcoverRadiusLedgerTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FiniteSubcoverRadiusLedgerUp} :
    finiteSubcoverRadiusLedgerToEventFlow x =
        finiteSubcoverRadiusLedgerToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteSubcoverRadiusLedgerFromEventFlow (finiteSubcoverRadiusLedgerToEventFlow x) =
        finiteSubcoverRadiusLedgerFromEventFlow (finiteSubcoverRadiusLedgerToEventFlow y) :=
    congrArg finiteSubcoverRadiusLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (FiniteSubcoverRadiusLedgerTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (FiniteSubcoverRadiusLedgerTasteGate_single_carrier_alignment_round_trip y)))

private def finiteSubcoverRadiusLedgerFields :
    FiniteSubcoverRadiusLedgerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteSubcoverRadiusLedgerUp.mk K F G R B U H C P N =>
      [K, F, G, R, B, U, H, C, P, N]

private theorem FiniteSubcoverRadiusLedgerTasteGate_single_carrier_alignment_fields :
    ∀ x y : FiniteSubcoverRadiusLedgerUp,
      finiteSubcoverRadiusLedgerFields x = finiteSubcoverRadiusLedgerFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K1 F1 G1 R1 B1 U1 H1 C1 P1 N1 =>
      cases y with
      | mk K2 F2 G2 R2 B2 U2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance finiteSubcoverRadiusLedgerBHistCarrier :
    BHistCarrier FiniteSubcoverRadiusLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteSubcoverRadiusLedgerToEventFlow
  fromEventFlow := finiteSubcoverRadiusLedgerFromEventFlow

instance finiteSubcoverRadiusLedgerChapterTasteGate :
    ChapterTasteGate FiniteSubcoverRadiusLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteSubcoverRadiusLedgerFromEventFlow
      (finiteSubcoverRadiusLedgerToEventFlow x) = some x
    exact FiniteSubcoverRadiusLedgerTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (FiniteSubcoverRadiusLedgerTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance finiteSubcoverRadiusLedgerFieldFaithful :
    FieldFaithful FiniteSubcoverRadiusLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteSubcoverRadiusLedgerFields
  field_faithful := FiniteSubcoverRadiusLedgerTasteGate_single_carrier_alignment_fields

instance finiteSubcoverRadiusLedgerNontrivial :
    BEDC.Meta.TasteGate.Nontrivial FiniteSubcoverRadiusLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteSubcoverRadiusLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FiniteSubcoverRadiusLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

theorem FiniteSubcoverRadiusLedgerTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate FiniteSubcoverRadiusLedgerUp) ∧
      Nonempty (FieldFaithful FiniteSubcoverRadiusLedgerUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial FiniteSubcoverRadiusLedgerUp) ∧
          finiteSubcoverRadiusLedgerEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∀ h : BHist,
              finiteSubcoverRadiusLedgerDecodeBHist
                (finiteSubcoverRadiusLedgerEncodeBHist h) = h) ∧
              (∀ x : FiniteSubcoverRadiusLedgerUp,
                finiteSubcoverRadiusLedgerFromEventFlow
                  (finiteSubcoverRadiusLedgerToEventFlow x) = some x) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨finiteSubcoverRadiusLedgerChapterTasteGate⟩,
      ⟨finiteSubcoverRadiusLedgerFieldFaithful⟩,
      ⟨finiteSubcoverRadiusLedgerNontrivial⟩,
      rfl,
      FiniteSubcoverRadiusLedgerTasteGate_single_carrier_alignment_decode,
      FiniteSubcoverRadiusLedgerTasteGate_single_carrier_alignment_round_trip⟩

end BEDC.Derived.FiniteSubcoverRadiusLedgerUp.TasteGate
