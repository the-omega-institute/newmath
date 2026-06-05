import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteOscillationPartitionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteOscillationPartitionUp : Type where
  | mk (I M A B R H C P N : BHist) : FiniteOscillationPartitionUp
  deriving DecidableEq

def finiteOscillationPartitionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteOscillationPartitionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteOscillationPartitionEncodeBHist h

def finiteOscillationPartitionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteOscillationPartitionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteOscillationPartitionDecodeBHist tail)

theorem finiteOscillationPartitionDecodeEncodeBHist :
    ∀ h : BHist,
      finiteOscillationPartitionDecodeBHist
          (finiteOscillationPartitionEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteOscillationPartitionFields :
    FiniteOscillationPartitionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteOscillationPartitionUp.mk I M A B R H C P N => [I, M, A, B, R, H, C, P, N]

def finiteOscillationPartitionToEventFlow :
    FiniteOscillationPartitionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (finiteOscillationPartitionFields x).map finiteOscillationPartitionEncodeBHist

def finiteOscillationPartitionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => finiteOscillationPartitionEventAt index rest

def finiteOscillationPartitionFromEventFlow :
    EventFlow → Option FiniteOscillationPartitionUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      some
        (FiniteOscillationPartitionUp.mk
          (finiteOscillationPartitionDecodeBHist (finiteOscillationPartitionEventAt 0 flow))
          (finiteOscillationPartitionDecodeBHist (finiteOscillationPartitionEventAt 1 flow))
          (finiteOscillationPartitionDecodeBHist (finiteOscillationPartitionEventAt 2 flow))
          (finiteOscillationPartitionDecodeBHist (finiteOscillationPartitionEventAt 3 flow))
          (finiteOscillationPartitionDecodeBHist (finiteOscillationPartitionEventAt 4 flow))
          (finiteOscillationPartitionDecodeBHist (finiteOscillationPartitionEventAt 5 flow))
          (finiteOscillationPartitionDecodeBHist (finiteOscillationPartitionEventAt 6 flow))
          (finiteOscillationPartitionDecodeBHist (finiteOscillationPartitionEventAt 7 flow))
          (finiteOscillationPartitionDecodeBHist (finiteOscillationPartitionEventAt 8 flow)))

private theorem finiteOscillationPartition_round_trip :
    ∀ x : FiniteOscillationPartitionUp,
      finiteOscillationPartitionFromEventFlow
          (finiteOscillationPartitionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I M A B R H C P N =>
      change
        some
          (FiniteOscillationPartitionUp.mk
            (finiteOscillationPartitionDecodeBHist
              (finiteOscillationPartitionEncodeBHist I))
            (finiteOscillationPartitionDecodeBHist
              (finiteOscillationPartitionEncodeBHist M))
            (finiteOscillationPartitionDecodeBHist
              (finiteOscillationPartitionEncodeBHist A))
            (finiteOscillationPartitionDecodeBHist
              (finiteOscillationPartitionEncodeBHist B))
            (finiteOscillationPartitionDecodeBHist
              (finiteOscillationPartitionEncodeBHist R))
            (finiteOscillationPartitionDecodeBHist
              (finiteOscillationPartitionEncodeBHist H))
            (finiteOscillationPartitionDecodeBHist
              (finiteOscillationPartitionEncodeBHist C))
            (finiteOscillationPartitionDecodeBHist
              (finiteOscillationPartitionEncodeBHist P))
            (finiteOscillationPartitionDecodeBHist
              (finiteOscillationPartitionEncodeBHist N))) =
          some (FiniteOscillationPartitionUp.mk I M A B R H C P N)
      rw [finiteOscillationPartitionDecodeEncodeBHist I,
        finiteOscillationPartitionDecodeEncodeBHist M,
        finiteOscillationPartitionDecodeEncodeBHist A,
        finiteOscillationPartitionDecodeEncodeBHist B,
        finiteOscillationPartitionDecodeEncodeBHist R,
        finiteOscillationPartitionDecodeEncodeBHist H,
        finiteOscillationPartitionDecodeEncodeBHist C,
        finiteOscillationPartitionDecodeEncodeBHist P,
        finiteOscillationPartitionDecodeEncodeBHist N]

private theorem finiteOscillationPartitionToEventFlow_injective
    {x y : FiniteOscillationPartitionUp} :
    finiteOscillationPartitionToEventFlow x =
        finiteOscillationPartitionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteOscillationPartitionFromEventFlow
          (finiteOscillationPartitionToEventFlow x) =
        finiteOscillationPartitionFromEventFlow
          (finiteOscillationPartitionToEventFlow y) :=
    congrArg finiteOscillationPartitionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finiteOscillationPartition_round_trip x).symm
      (Eq.trans hread (finiteOscillationPartition_round_trip y)))

private theorem finiteOscillationPartition_fields_faithful :
    ∀ x y : FiniteOscillationPartitionUp,
      finiteOscillationPartitionFields x =
          finiteOscillationPartitionFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I1 M1 A1 B1 R1 H1 C1 P1 N1 =>
      cases y with
      | mk I2 M2 A2 B2 R2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance finiteOscillationPartitionBHistCarrier :
    BHistCarrier FiniteOscillationPartitionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteOscillationPartitionToEventFlow
  fromEventFlow := finiteOscillationPartitionFromEventFlow

instance finiteOscillationPartitionChapterTasteGate :
    ChapterTasteGate FiniteOscillationPartitionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      finiteOscillationPartitionFromEventFlow
          (finiteOscillationPartitionToEventFlow x) =
        some x
    exact finiteOscillationPartition_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteOscillationPartitionToEventFlow_injective heq)

instance finiteOscillationPartitionFieldFaithful :
    FieldFaithful FiniteOscillationPartitionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteOscillationPartitionFields
  field_faithful := finiteOscillationPartition_fields_faithful

instance finiteOscillationPartitionNontrivial :
    BEDC.Meta.TasteGate.Nontrivial FiniteOscillationPartitionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteOscillationPartitionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FiniteOscillationPartitionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def finiteOscillationPartitionTasteGate :
    ChapterTasteGate FiniteOscillationPartitionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteOscillationPartitionChapterTasteGate

theorem FiniteOscillationPartitionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        finiteOscillationPartitionDecodeBHist
            (finiteOscillationPartitionEncodeBHist h) =
          h) ∧
      Nonempty (ChapterTasteGate FiniteOscillationPartitionUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial FiniteOscillationPartitionUp) ∧
          Nonempty (BEDC.Meta.TasteGate.FieldFaithful FiniteOscillationPartitionUp) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  constructor
  · exact finiteOscillationPartitionDecodeEncodeBHist
  · constructor
    · exact ⟨finiteOscillationPartitionChapterTasteGate⟩
    · constructor
      · exact ⟨finiteOscillationPartitionNontrivial⟩
      · exact ⟨finiteOscillationPartitionFieldFaithful⟩

end BEDC.Derived.FiniteOscillationPartitionUp
