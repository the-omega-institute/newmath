import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DiagonalIndexCofinalityUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DiagonalIndexCofinalityUp : Type where
  | mk (X mu n k i W R D E H C P N : BHist) : DiagonalIndexCofinalityUp
  deriving DecidableEq

def diagonalIndexCofinalityEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: diagonalIndexCofinalityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: diagonalIndexCofinalityEncodeBHist h

def diagonalIndexCofinalityDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (diagonalIndexCofinalityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (diagonalIndexCofinalityDecodeBHist tail)

private theorem DiagonalIndexCofinalityTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      diagonalIndexCofinalityDecodeBHist
        (diagonalIndexCofinalityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def diagonalIndexCofinalityFields : DiagonalIndexCofinalityUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DiagonalIndexCofinalityUp.mk X mu n k i W R D E H C P N =>
      [X, mu, n, k, i, W, R, D, E, H, C, P, N]

def diagonalIndexCofinalityToEventFlow : DiagonalIndexCofinalityUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (diagonalIndexCofinalityFields x).map diagonalIndexCofinalityEncodeBHist

private def diagonalIndexCofinalityEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => diagonalIndexCofinalityEventAtDefault index rest

def diagonalIndexCofinalityFromEventFlow
    (ef : EventFlow) : Option DiagonalIndexCofinalityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DiagonalIndexCofinalityUp.mk
      (diagonalIndexCofinalityDecodeBHist (diagonalIndexCofinalityEventAtDefault 0 ef))
      (diagonalIndexCofinalityDecodeBHist (diagonalIndexCofinalityEventAtDefault 1 ef))
      (diagonalIndexCofinalityDecodeBHist (diagonalIndexCofinalityEventAtDefault 2 ef))
      (diagonalIndexCofinalityDecodeBHist (diagonalIndexCofinalityEventAtDefault 3 ef))
      (diagonalIndexCofinalityDecodeBHist (diagonalIndexCofinalityEventAtDefault 4 ef))
      (diagonalIndexCofinalityDecodeBHist (diagonalIndexCofinalityEventAtDefault 5 ef))
      (diagonalIndexCofinalityDecodeBHist (diagonalIndexCofinalityEventAtDefault 6 ef))
      (diagonalIndexCofinalityDecodeBHist (diagonalIndexCofinalityEventAtDefault 7 ef))
      (diagonalIndexCofinalityDecodeBHist (diagonalIndexCofinalityEventAtDefault 8 ef))
      (diagonalIndexCofinalityDecodeBHist (diagonalIndexCofinalityEventAtDefault 9 ef))
      (diagonalIndexCofinalityDecodeBHist (diagonalIndexCofinalityEventAtDefault 10 ef))
      (diagonalIndexCofinalityDecodeBHist (diagonalIndexCofinalityEventAtDefault 11 ef))
      (diagonalIndexCofinalityDecodeBHist (diagonalIndexCofinalityEventAtDefault 12 ef)))

private theorem DiagonalIndexCofinalityTasteGate_single_carrier_alignment_round_trip :
    forall x : DiagonalIndexCofinalityUp,
      diagonalIndexCofinalityFromEventFlow
        (diagonalIndexCofinalityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro packet
  cases packet with
  | mk X mu n k i W R D E H C P N =>
      change
        some
          (DiagonalIndexCofinalityUp.mk
            (diagonalIndexCofinalityDecodeBHist (diagonalIndexCofinalityEncodeBHist X))
            (diagonalIndexCofinalityDecodeBHist (diagonalIndexCofinalityEncodeBHist mu))
            (diagonalIndexCofinalityDecodeBHist (diagonalIndexCofinalityEncodeBHist n))
            (diagonalIndexCofinalityDecodeBHist (diagonalIndexCofinalityEncodeBHist k))
            (diagonalIndexCofinalityDecodeBHist (diagonalIndexCofinalityEncodeBHist i))
            (diagonalIndexCofinalityDecodeBHist (diagonalIndexCofinalityEncodeBHist W))
            (diagonalIndexCofinalityDecodeBHist (diagonalIndexCofinalityEncodeBHist R))
            (diagonalIndexCofinalityDecodeBHist (diagonalIndexCofinalityEncodeBHist D))
            (diagonalIndexCofinalityDecodeBHist (diagonalIndexCofinalityEncodeBHist E))
            (diagonalIndexCofinalityDecodeBHist (diagonalIndexCofinalityEncodeBHist H))
            (diagonalIndexCofinalityDecodeBHist (diagonalIndexCofinalityEncodeBHist C))
            (diagonalIndexCofinalityDecodeBHist (diagonalIndexCofinalityEncodeBHist P))
            (diagonalIndexCofinalityDecodeBHist (diagonalIndexCofinalityEncodeBHist N))) =
          some (DiagonalIndexCofinalityUp.mk X mu n k i W R D E H C P N)
      rw [DiagonalIndexCofinalityTasteGate_single_carrier_alignment_decode X,
        DiagonalIndexCofinalityTasteGate_single_carrier_alignment_decode mu,
        DiagonalIndexCofinalityTasteGate_single_carrier_alignment_decode n,
        DiagonalIndexCofinalityTasteGate_single_carrier_alignment_decode k,
        DiagonalIndexCofinalityTasteGate_single_carrier_alignment_decode i,
        DiagonalIndexCofinalityTasteGate_single_carrier_alignment_decode W,
        DiagonalIndexCofinalityTasteGate_single_carrier_alignment_decode R,
        DiagonalIndexCofinalityTasteGate_single_carrier_alignment_decode D,
        DiagonalIndexCofinalityTasteGate_single_carrier_alignment_decode E,
        DiagonalIndexCofinalityTasteGate_single_carrier_alignment_decode H,
        DiagonalIndexCofinalityTasteGate_single_carrier_alignment_decode C,
        DiagonalIndexCofinalityTasteGate_single_carrier_alignment_decode P,
        DiagonalIndexCofinalityTasteGate_single_carrier_alignment_decode N]

private theorem DiagonalIndexCofinalityToEventFlow_injective {x y : DiagonalIndexCofinalityUp} :
    diagonalIndexCofinalityToEventFlow x = diagonalIndexCofinalityToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      diagonalIndexCofinalityFromEventFlow (diagonalIndexCofinalityToEventFlow x) =
        diagonalIndexCofinalityFromEventFlow (diagonalIndexCofinalityToEventFlow y) :=
    congrArg diagonalIndexCofinalityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (DiagonalIndexCofinalityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (DiagonalIndexCofinalityTasteGate_single_carrier_alignment_round_trip y)))

private theorem DiagonalIndexCofinalityTasteGate_single_carrier_alignment_fields :
    forall x y : DiagonalIndexCofinalityUp,
      diagonalIndexCofinalityFields x = diagonalIndexCofinalityFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 mu1 n1 k1 i1 W1 R1 D1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk X2 mu2 n2 k2 i2 W2 R2 D2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance diagonalIndexCofinalityBHistCarrier :
    BHistCarrier DiagonalIndexCofinalityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := diagonalIndexCofinalityToEventFlow
  fromEventFlow := diagonalIndexCofinalityFromEventFlow

instance diagonalIndexCofinalityChapterTasteGate :
    ChapterTasteGate DiagonalIndexCofinalityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      diagonalIndexCofinalityFromEventFlow (diagonalIndexCofinalityToEventFlow x) =
        some x
    exact DiagonalIndexCofinalityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DiagonalIndexCofinalityToEventFlow_injective heq)

def taste_gate : ChapterTasteGate DiagonalIndexCofinalityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  diagonalIndexCofinalityChapterTasteGate

instance diagonalIndexCofinalityFieldFaithful :
    FieldFaithful DiagonalIndexCofinalityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := diagonalIndexCofinalityFields
  field_faithful := DiagonalIndexCofinalityTasteGate_single_carrier_alignment_fields

instance diagonalIndexCofinalityNontrivial :
    Nontrivial DiagonalIndexCofinalityUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DiagonalIndexCofinalityUp.mk
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DiagonalIndexCofinalityUp.mk
        (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem DiagonalIndexCofinalityTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate DiagonalIndexCofinalityUp) ∧
      Nonempty (FieldFaithful DiagonalIndexCofinalityUp) ∧
        Nonempty (Nontrivial DiagonalIndexCofinalityUp) ∧
          (∀ h : BHist,
            diagonalIndexCofinalityDecodeBHist
              (diagonalIndexCofinalityEncodeBHist h) = h) ∧
            (∀ x : DiagonalIndexCofinalityUp,
              diagonalIndexCofinalityFromEventFlow
                (diagonalIndexCofinalityToEventFlow x) = some x) ∧
              (∀ x y : DiagonalIndexCofinalityUp,
                diagonalIndexCofinalityToEventFlow x =
                  diagonalIndexCofinalityToEventFlow y -> x = y) ∧
                diagonalIndexCofinalityEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate Nontrivial
  exact
    ⟨⟨diagonalIndexCofinalityChapterTasteGate⟩,
      ⟨diagonalIndexCofinalityFieldFaithful⟩,
      ⟨diagonalIndexCofinalityNontrivial⟩,
      DiagonalIndexCofinalityTasteGate_single_carrier_alignment_decode,
      DiagonalIndexCofinalityTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => DiagonalIndexCofinalityToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.DiagonalIndexCofinalityUp.TasteGate
