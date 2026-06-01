import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteVolumeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteVolumeUp : Type where
  | mk (M F X B S R D E H C P N : BHist) : FiniteVolumeUp
  deriving DecidableEq

def finiteVolumeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteVolumeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteVolumeEncodeBHist h

def finiteVolumeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteVolumeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteVolumeDecodeBHist tail)

private theorem finiteVolumeDecode_encode_bhist :
    ∀ h : BHist, finiteVolumeDecodeBHist (finiteVolumeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteVolumeFields : FiniteVolumeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteVolumeUp.mk M F X B S R D E H C P N => [M, F, X, B, S, R, D, E, H, C, P, N]

def finiteVolumeToEventFlow : FiniteVolumeUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (finiteVolumeFields x).map finiteVolumeEncodeBHist

private def finiteVolumeEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => finiteVolumeEventAtDefault index rest

def finiteVolumeFromEventFlow (ef : EventFlow) : Option FiniteVolumeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FiniteVolumeUp.mk
      (finiteVolumeDecodeBHist (finiteVolumeEventAtDefault 0 ef))
      (finiteVolumeDecodeBHist (finiteVolumeEventAtDefault 1 ef))
      (finiteVolumeDecodeBHist (finiteVolumeEventAtDefault 2 ef))
      (finiteVolumeDecodeBHist (finiteVolumeEventAtDefault 3 ef))
      (finiteVolumeDecodeBHist (finiteVolumeEventAtDefault 4 ef))
      (finiteVolumeDecodeBHist (finiteVolumeEventAtDefault 5 ef))
      (finiteVolumeDecodeBHist (finiteVolumeEventAtDefault 6 ef))
      (finiteVolumeDecodeBHist (finiteVolumeEventAtDefault 7 ef))
      (finiteVolumeDecodeBHist (finiteVolumeEventAtDefault 8 ef))
      (finiteVolumeDecodeBHist (finiteVolumeEventAtDefault 9 ef))
      (finiteVolumeDecodeBHist (finiteVolumeEventAtDefault 10 ef))
      (finiteVolumeDecodeBHist (finiteVolumeEventAtDefault 11 ef)))

private theorem finiteVolume_round_trip :
    ∀ x : FiniteVolumeUp, finiteVolumeFromEventFlow (finiteVolumeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M F X B S R D E H C P N =>
      change
        some
          (FiniteVolumeUp.mk
            (finiteVolumeDecodeBHist (finiteVolumeEncodeBHist M))
            (finiteVolumeDecodeBHist (finiteVolumeEncodeBHist F))
            (finiteVolumeDecodeBHist (finiteVolumeEncodeBHist X))
            (finiteVolumeDecodeBHist (finiteVolumeEncodeBHist B))
            (finiteVolumeDecodeBHist (finiteVolumeEncodeBHist S))
            (finiteVolumeDecodeBHist (finiteVolumeEncodeBHist R))
            (finiteVolumeDecodeBHist (finiteVolumeEncodeBHist D))
            (finiteVolumeDecodeBHist (finiteVolumeEncodeBHist E))
            (finiteVolumeDecodeBHist (finiteVolumeEncodeBHist H))
            (finiteVolumeDecodeBHist (finiteVolumeEncodeBHist C))
            (finiteVolumeDecodeBHist (finiteVolumeEncodeBHist P))
            (finiteVolumeDecodeBHist (finiteVolumeEncodeBHist N))) =
          some (FiniteVolumeUp.mk M F X B S R D E H C P N)
      rw [finiteVolumeDecode_encode_bhist M, finiteVolumeDecode_encode_bhist F,
        finiteVolumeDecode_encode_bhist X, finiteVolumeDecode_encode_bhist B,
        finiteVolumeDecode_encode_bhist S, finiteVolumeDecode_encode_bhist R,
        finiteVolumeDecode_encode_bhist D, finiteVolumeDecode_encode_bhist E,
        finiteVolumeDecode_encode_bhist H, finiteVolumeDecode_encode_bhist C,
        finiteVolumeDecode_encode_bhist P, finiteVolumeDecode_encode_bhist N]

private theorem finiteVolumeToEventFlow_injective {x y : FiniteVolumeUp} :
    finiteVolumeToEventFlow x = finiteVolumeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteVolumeFromEventFlow (finiteVolumeToEventFlow x) =
        finiteVolumeFromEventFlow (finiteVolumeToEventFlow y) :=
    congrArg finiteVolumeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finiteVolume_round_trip x).symm (Eq.trans hread (finiteVolume_round_trip y)))

private theorem finiteVolume_fields_faithful :
    ∀ x y : FiniteVolumeUp, finiteVolumeFields x = finiteVolumeFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M1 F1 X1 B1 S1 R1 D1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk M2 F2 X2 B2 S2 R2 D2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance finiteVolumeBHistCarrier : BHistCarrier FiniteVolumeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteVolumeToEventFlow
  fromEventFlow := finiteVolumeFromEventFlow

instance finiteVolumeChapterTasteGate : ChapterTasteGate FiniteVolumeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteVolumeFromEventFlow (finiteVolumeToEventFlow x) = some x
    exact finiteVolume_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteVolumeToEventFlow_injective heq)

instance finiteVolumeFieldFaithful : FieldFaithful FiniteVolumeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteVolumeFields
  field_faithful := finiteVolume_fields_faithful

def taste_gate : ChapterTasteGate FiniteVolumeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteVolumeChapterTasteGate

theorem FiniteVolumeTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate FiniteVolumeUp) ∧ Nonempty (BHistCarrier FiniteVolumeUp) ∧
      (∀ h : BHist, finiteVolumeDecodeBHist (finiteVolumeEncodeBHist h) = h) ∧
        finiteVolumeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate BHistCarrier
  exact
    ⟨⟨finiteVolumeChapterTasteGate⟩, ⟨finiteVolumeBHistCarrier⟩,
      finiteVolumeDecode_encode_bhist, rfl⟩

end BEDC.Derived.FiniteVolumeUp
