import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteObservationFoldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteObservationFoldUp : Type where
  | mk (K T R N S G H C P L : BHist) : FiniteObservationFoldUp
  deriving DecidableEq

def finiteObservationFoldEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteObservationFoldEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteObservationFoldEncodeBHist h

def finiteObservationFoldDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteObservationFoldDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteObservationFoldDecodeBHist tail)

private theorem FiniteObservationFoldTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, finiteObservationFoldDecodeBHist (finiteObservationFoldEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteObservationFoldFields : FiniteObservationFoldUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteObservationFoldUp.mk K T R N S G H C P L => [K, T, R, N, S, G, H, C, P, L]

def finiteObservationFoldToEventFlow : FiniteObservationFoldUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (finiteObservationFoldFields x).map finiteObservationFoldEncodeBHist

def finiteObservationFoldEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => finiteObservationFoldEventAt index rest

def finiteObservationFoldFromEventFlow : EventFlow → Option FiniteObservationFoldUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      some
        (FiniteObservationFoldUp.mk
          (finiteObservationFoldDecodeBHist (finiteObservationFoldEventAt 0 flow))
          (finiteObservationFoldDecodeBHist (finiteObservationFoldEventAt 1 flow))
          (finiteObservationFoldDecodeBHist (finiteObservationFoldEventAt 2 flow))
          (finiteObservationFoldDecodeBHist (finiteObservationFoldEventAt 3 flow))
          (finiteObservationFoldDecodeBHist (finiteObservationFoldEventAt 4 flow))
          (finiteObservationFoldDecodeBHist (finiteObservationFoldEventAt 5 flow))
          (finiteObservationFoldDecodeBHist (finiteObservationFoldEventAt 6 flow))
          (finiteObservationFoldDecodeBHist (finiteObservationFoldEventAt 7 flow))
          (finiteObservationFoldDecodeBHist (finiteObservationFoldEventAt 8 flow))
          (finiteObservationFoldDecodeBHist (finiteObservationFoldEventAt 9 flow)))

private theorem FiniteObservationFoldTasteGate_single_carrier_alignment_round_trip :
    ∀ x : FiniteObservationFoldUp,
      finiteObservationFoldFromEventFlow (finiteObservationFoldToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K T R N S G H C P L =>
      change
        some
          (FiniteObservationFoldUp.mk
            (finiteObservationFoldDecodeBHist (finiteObservationFoldEncodeBHist K))
            (finiteObservationFoldDecodeBHist (finiteObservationFoldEncodeBHist T))
            (finiteObservationFoldDecodeBHist (finiteObservationFoldEncodeBHist R))
            (finiteObservationFoldDecodeBHist (finiteObservationFoldEncodeBHist N))
            (finiteObservationFoldDecodeBHist (finiteObservationFoldEncodeBHist S))
            (finiteObservationFoldDecodeBHist (finiteObservationFoldEncodeBHist G))
            (finiteObservationFoldDecodeBHist (finiteObservationFoldEncodeBHist H))
            (finiteObservationFoldDecodeBHist (finiteObservationFoldEncodeBHist C))
            (finiteObservationFoldDecodeBHist (finiteObservationFoldEncodeBHist P))
            (finiteObservationFoldDecodeBHist (finiteObservationFoldEncodeBHist L))) =
          some (FiniteObservationFoldUp.mk K T R N S G H C P L)
      rw [FiniteObservationFoldTasteGate_single_carrier_alignment_decode K,
        FiniteObservationFoldTasteGate_single_carrier_alignment_decode T,
        FiniteObservationFoldTasteGate_single_carrier_alignment_decode R,
        FiniteObservationFoldTasteGate_single_carrier_alignment_decode N,
        FiniteObservationFoldTasteGate_single_carrier_alignment_decode S,
        FiniteObservationFoldTasteGate_single_carrier_alignment_decode G,
        FiniteObservationFoldTasteGate_single_carrier_alignment_decode H,
        FiniteObservationFoldTasteGate_single_carrier_alignment_decode C,
        FiniteObservationFoldTasteGate_single_carrier_alignment_decode P,
        FiniteObservationFoldTasteGate_single_carrier_alignment_decode L]

private theorem finiteObservationFoldToEventFlow_injective {x y : FiniteObservationFoldUp} :
    finiteObservationFoldToEventFlow x = finiteObservationFoldToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteObservationFoldFromEventFlow (finiteObservationFoldToEventFlow x) =
        finiteObservationFoldFromEventFlow (finiteObservationFoldToEventFlow y) :=
    congrArg finiteObservationFoldFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (FiniteObservationFoldTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (FiniteObservationFoldTasteGate_single_carrier_alignment_round_trip y)))

private theorem FiniteObservationFoldTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : FiniteObservationFoldUp, finiteObservationFoldFields x = finiteObservationFoldFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K1 T1 R1 N1 S1 G1 H1 C1 P1 L1 =>
      cases y with
      | mk K2 T2 R2 N2 S2 G2 H2 C2 P2 L2 =>
          cases hfields
          rfl

instance finiteObservationFoldBHistCarrier : BHistCarrier FiniteObservationFoldUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteObservationFoldToEventFlow
  fromEventFlow := finiteObservationFoldFromEventFlow

instance finiteObservationFoldChapterTasteGate : ChapterTasteGate FiniteObservationFoldUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteObservationFoldFromEventFlow (finiteObservationFoldToEventFlow x) = some x
    exact FiniteObservationFoldTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteObservationFoldToEventFlow_injective heq)

instance finiteObservationFoldFieldFaithful : FieldFaithful FiniteObservationFoldUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteObservationFoldFields
  field_faithful := FiniteObservationFoldTasteGate_single_carrier_alignment_fields_faithful

instance finiteObservationFoldNontrivial : Nontrivial FiniteObservationFoldUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteObservationFoldUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FiniteObservationFoldUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FiniteObservationFoldUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteObservationFoldChapterTasteGate

theorem FiniteObservationFoldTasteGate_single_carrier_alignment :
    (forall h : BHist, finiteObservationFoldDecodeBHist (finiteObservationFoldEncodeBHist h) = h) ∧
      finiteObservationFoldFields
          (FiniteObservationFoldUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  exact ⟨FiniteObservationFoldTasteGate_single_carrier_alignment_decode, rfl⟩

end BEDC.Derived.FiniteObservationFoldUp
