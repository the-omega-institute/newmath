import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteIntervalCoverUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteIntervalCoverUp : Type where
  | mk (I D B W C R E H K P N : BHist) : FiniteIntervalCoverUp
  deriving DecidableEq

def finiteIntervalCoverEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteIntervalCoverEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteIntervalCoverEncodeBHist h

def finiteIntervalCoverDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteIntervalCoverDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteIntervalCoverDecodeBHist tail)

private theorem FiniteIntervalCoverTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      finiteIntervalCoverDecodeBHist (finiteIntervalCoverEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def FiniteIntervalCoverTasteGate_single_carrier_alignment_fields :
    FiniteIntervalCoverUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteIntervalCoverUp.mk I D B W C R E H K P N =>
      [I, D, B, W, C, R, E, H, K, P, N]

def finiteIntervalCoverToEventFlow : FiniteIntervalCoverUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | token =>
      (FiniteIntervalCoverTasteGate_single_carrier_alignment_fields token).map
        finiteIntervalCoverEncodeBHist

private def finiteIntervalCoverEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => finiteIntervalCoverEventAtDefault index rest

def finiteIntervalCoverFromEventFlow
    (ef : EventFlow) : Option FiniteIntervalCoverUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FiniteIntervalCoverUp.mk
      (finiteIntervalCoverDecodeBHist (finiteIntervalCoverEventAtDefault 0 ef))
      (finiteIntervalCoverDecodeBHist (finiteIntervalCoverEventAtDefault 1 ef))
      (finiteIntervalCoverDecodeBHist (finiteIntervalCoverEventAtDefault 2 ef))
      (finiteIntervalCoverDecodeBHist (finiteIntervalCoverEventAtDefault 3 ef))
      (finiteIntervalCoverDecodeBHist (finiteIntervalCoverEventAtDefault 4 ef))
      (finiteIntervalCoverDecodeBHist (finiteIntervalCoverEventAtDefault 5 ef))
      (finiteIntervalCoverDecodeBHist (finiteIntervalCoverEventAtDefault 6 ef))
      (finiteIntervalCoverDecodeBHist (finiteIntervalCoverEventAtDefault 7 ef))
      (finiteIntervalCoverDecodeBHist (finiteIntervalCoverEventAtDefault 8 ef))
      (finiteIntervalCoverDecodeBHist (finiteIntervalCoverEventAtDefault 9 ef))
      (finiteIntervalCoverDecodeBHist (finiteIntervalCoverEventAtDefault 10 ef)))

private theorem finiteIntervalCover_round_trip :
    ∀ token : FiniteIntervalCoverUp,
      finiteIntervalCoverFromEventFlow (finiteIntervalCoverToEventFlow token) =
        some token := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk I D B W C R E H K P N =>
      change
        some
          (FiniteIntervalCoverUp.mk
            (finiteIntervalCoverDecodeBHist (finiteIntervalCoverEncodeBHist I))
            (finiteIntervalCoverDecodeBHist (finiteIntervalCoverEncodeBHist D))
            (finiteIntervalCoverDecodeBHist (finiteIntervalCoverEncodeBHist B))
            (finiteIntervalCoverDecodeBHist (finiteIntervalCoverEncodeBHist W))
            (finiteIntervalCoverDecodeBHist (finiteIntervalCoverEncodeBHist C))
            (finiteIntervalCoverDecodeBHist (finiteIntervalCoverEncodeBHist R))
            (finiteIntervalCoverDecodeBHist (finiteIntervalCoverEncodeBHist E))
            (finiteIntervalCoverDecodeBHist (finiteIntervalCoverEncodeBHist H))
            (finiteIntervalCoverDecodeBHist (finiteIntervalCoverEncodeBHist K))
            (finiteIntervalCoverDecodeBHist (finiteIntervalCoverEncodeBHist P))
            (finiteIntervalCoverDecodeBHist (finiteIntervalCoverEncodeBHist N))) =
          some (FiniteIntervalCoverUp.mk I D B W C R E H K P N)
      rw [FiniteIntervalCoverTasteGate_single_carrier_alignment_decode_encode I,
        FiniteIntervalCoverTasteGate_single_carrier_alignment_decode_encode D,
        FiniteIntervalCoverTasteGate_single_carrier_alignment_decode_encode B,
        FiniteIntervalCoverTasteGate_single_carrier_alignment_decode_encode W,
        FiniteIntervalCoverTasteGate_single_carrier_alignment_decode_encode C,
        FiniteIntervalCoverTasteGate_single_carrier_alignment_decode_encode R,
        FiniteIntervalCoverTasteGate_single_carrier_alignment_decode_encode E,
        FiniteIntervalCoverTasteGate_single_carrier_alignment_decode_encode H,
        FiniteIntervalCoverTasteGate_single_carrier_alignment_decode_encode K,
        FiniteIntervalCoverTasteGate_single_carrier_alignment_decode_encode P,
        FiniteIntervalCoverTasteGate_single_carrier_alignment_decode_encode N]

private theorem finiteIntervalCoverToEventFlow_injective
    {x y : FiniteIntervalCoverUp} :
    finiteIntervalCoverToEventFlow x = finiteIntervalCoverToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteIntervalCoverFromEventFlow (finiteIntervalCoverToEventFlow x) =
        finiteIntervalCoverFromEventFlow (finiteIntervalCoverToEventFlow y) :=
    congrArg finiteIntervalCoverFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finiteIntervalCover_round_trip x).symm
      (Eq.trans hread (finiteIntervalCover_round_trip y)))

private theorem finiteIntervalCover_fields_faithful
    {x y : FiniteIntervalCoverUp} :
    FiniteIntervalCoverTasteGate_single_carrier_alignment_fields x =
      FiniteIntervalCoverTasteGate_single_carrier_alignment_fields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hfields
  cases x with
  | mk I1 D1 B1 W1 C1 R1 E1 H1 K1 P1 N1 =>
      cases y with
      | mk I2 D2 B2 W2 C2 R2 E2 H2 K2 P2 N2 =>
          cases hfields
          rfl

instance finiteIntervalCoverBHistCarrier : BHistCarrier FiniteIntervalCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteIntervalCoverToEventFlow
  fromEventFlow := finiteIntervalCoverFromEventFlow

instance finiteIntervalCoverChapterTasteGate : ChapterTasteGate FiniteIntervalCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteIntervalCoverFromEventFlow (finiteIntervalCoverToEventFlow x) = some x
    exact finiteIntervalCover_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteIntervalCoverToEventFlow_injective heq)

instance finiteIntervalCoverFieldFaithful : FieldFaithful FiniteIntervalCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := FiniteIntervalCoverTasteGate_single_carrier_alignment_fields
  field_faithful := by
    intro x y h
    exact finiteIntervalCover_fields_faithful h

def taste_gate : ChapterTasteGate FiniteIntervalCoverUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteIntervalCoverChapterTasteGate

theorem FiniteIntervalCoverTasteGate_single_carrier_alignment :
    (∀ I D B W C R E H K P N : BHist,
      FiniteIntervalCoverTasteGate_single_carrier_alignment_fields
          (FiniteIntervalCoverUp.mk I D B W C R E H K P N) =
        [I, D, B, W, C, R, E, H, K, P, N]) ∧
      (∀ h : BHist,
        finiteIntervalCoverDecodeBHist (finiteIntervalCoverEncodeBHist h) = h) ∧
        finiteIntervalCoverEncodeBHist (BHist.e1 BHist.Empty) = [BMark.b1] := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  exact
    ⟨(by
        intro I D B W C R E H K P N
        rfl),
      FiniteIntervalCoverTasteGate_single_carrier_alignment_decode_encode,
      rfl⟩

end BEDC.Derived.FiniteIntervalCoverUp
