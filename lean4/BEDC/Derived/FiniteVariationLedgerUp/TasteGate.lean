import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteVariationLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteVariationLedgerUp : Type where
  | mk (I Pi X D V R H C P N : BHist) : FiniteVariationLedgerUp
  deriving DecidableEq

def finiteVariationLedgerEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteVariationLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteVariationLedgerEncodeBHist h

def finiteVariationLedgerDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteVariationLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteVariationLedgerDecodeBHist tail)

private theorem FiniteVariationLedgerTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      finiteVariationLedgerDecodeBHist (finiteVariationLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteVariationLedgerFields : FiniteVariationLedgerUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteVariationLedgerUp.mk I Pi X D V R H C P N => [I, Pi, X, D, V, R, H, C, P, N]

def finiteVariationLedgerToEventFlow : FiniteVariationLedgerUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (finiteVariationLedgerFields x).map finiteVariationLedgerEncodeBHist

private def finiteVariationLedgerEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => finiteVariationLedgerEventAtDefault index rest

def finiteVariationLedgerFromEventFlow (ef : EventFlow) : Option FiniteVariationLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FiniteVariationLedgerUp.mk
      (finiteVariationLedgerDecodeBHist (finiteVariationLedgerEventAtDefault 0 ef))
      (finiteVariationLedgerDecodeBHist (finiteVariationLedgerEventAtDefault 1 ef))
      (finiteVariationLedgerDecodeBHist (finiteVariationLedgerEventAtDefault 2 ef))
      (finiteVariationLedgerDecodeBHist (finiteVariationLedgerEventAtDefault 3 ef))
      (finiteVariationLedgerDecodeBHist (finiteVariationLedgerEventAtDefault 4 ef))
      (finiteVariationLedgerDecodeBHist (finiteVariationLedgerEventAtDefault 5 ef))
      (finiteVariationLedgerDecodeBHist (finiteVariationLedgerEventAtDefault 6 ef))
      (finiteVariationLedgerDecodeBHist (finiteVariationLedgerEventAtDefault 7 ef))
      (finiteVariationLedgerDecodeBHist (finiteVariationLedgerEventAtDefault 8 ef))
      (finiteVariationLedgerDecodeBHist (finiteVariationLedgerEventAtDefault 9 ef)))

private theorem FiniteVariationLedgerTasteGate_single_carrier_alignment_round_trip :
    forall x : FiniteVariationLedgerUp,
      finiteVariationLedgerFromEventFlow (finiteVariationLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I Pi X D V R H C P N =>
      change
        some
          (FiniteVariationLedgerUp.mk
            (finiteVariationLedgerDecodeBHist (finiteVariationLedgerEncodeBHist I))
            (finiteVariationLedgerDecodeBHist (finiteVariationLedgerEncodeBHist Pi))
            (finiteVariationLedgerDecodeBHist (finiteVariationLedgerEncodeBHist X))
            (finiteVariationLedgerDecodeBHist (finiteVariationLedgerEncodeBHist D))
            (finiteVariationLedgerDecodeBHist (finiteVariationLedgerEncodeBHist V))
            (finiteVariationLedgerDecodeBHist (finiteVariationLedgerEncodeBHist R))
            (finiteVariationLedgerDecodeBHist (finiteVariationLedgerEncodeBHist H))
            (finiteVariationLedgerDecodeBHist (finiteVariationLedgerEncodeBHist C))
            (finiteVariationLedgerDecodeBHist (finiteVariationLedgerEncodeBHist P))
            (finiteVariationLedgerDecodeBHist (finiteVariationLedgerEncodeBHist N))) =
          some (FiniteVariationLedgerUp.mk I Pi X D V R H C P N)
      rw [FiniteVariationLedgerTasteGate_single_carrier_alignment_decode I,
        FiniteVariationLedgerTasteGate_single_carrier_alignment_decode Pi,
        FiniteVariationLedgerTasteGate_single_carrier_alignment_decode X,
        FiniteVariationLedgerTasteGate_single_carrier_alignment_decode D,
        FiniteVariationLedgerTasteGate_single_carrier_alignment_decode V,
        FiniteVariationLedgerTasteGate_single_carrier_alignment_decode R,
        FiniteVariationLedgerTasteGate_single_carrier_alignment_decode H,
        FiniteVariationLedgerTasteGate_single_carrier_alignment_decode C,
        FiniteVariationLedgerTasteGate_single_carrier_alignment_decode P,
        FiniteVariationLedgerTasteGate_single_carrier_alignment_decode N]

private theorem FiniteVariationLedgerTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FiniteVariationLedgerUp} :
    finiteVariationLedgerToEventFlow x = finiteVariationLedgerToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteVariationLedgerFromEventFlow (finiteVariationLedgerToEventFlow x) =
        finiteVariationLedgerFromEventFlow (finiteVariationLedgerToEventFlow y) :=
    congrArg finiteVariationLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (FiniteVariationLedgerTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (FiniteVariationLedgerTasteGate_single_carrier_alignment_round_trip y)))

private theorem FiniteVariationLedgerTasteGate_single_carrier_alignment_fields :
    forall x y : FiniteVariationLedgerUp,
      finiteVariationLedgerFields x = finiteVariationLedgerFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk I1 Pi1 X1 D1 V1 R1 H1 C1 P1 N1 =>
      cases y with
      | mk I2 Pi2 X2 D2 V2 R2 H2 C2 P2 N2 =>
          cases h
          rfl

instance finiteVariationLedgerBHistCarrier : BHistCarrier FiniteVariationLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteVariationLedgerToEventFlow
  fromEventFlow := finiteVariationLedgerFromEventFlow

instance finiteVariationLedgerChapterTasteGate : ChapterTasteGate FiniteVariationLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteVariationLedgerFromEventFlow (finiteVariationLedgerToEventFlow x) = some x
    exact FiniteVariationLedgerTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FiniteVariationLedgerTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance finiteVariationLedgerFieldFaithful : FieldFaithful FiniteVariationLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteVariationLedgerFields
  field_faithful := FiniteVariationLedgerTasteGate_single_carrier_alignment_fields

def taste_gate : ChapterTasteGate FiniteVariationLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteVariationLedgerChapterTasteGate

theorem FiniteVariationLedgerTasteGate_single_carrier_alignment :
    (forall h : BHist, finiteVariationLedgerDecodeBHist (finiteVariationLedgerEncodeBHist h) = h) ∧
      (forall x : FiniteVariationLedgerUp,
        finiteVariationLedgerFromEventFlow (finiteVariationLedgerToEventFlow x) = some x) ∧
      (forall x y : FiniteVariationLedgerUp,
        finiteVariationLedgerToEventFlow x = finiteVariationLedgerToEventFlow y -> x = y) ∧
      (forall x y : FiniteVariationLedgerUp,
        finiteVariationLedgerFields x = finiteVariationLedgerFields y -> x = y) ∧
      finiteVariationLedgerEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  exact
    ⟨FiniteVariationLedgerTasteGate_single_carrier_alignment_decode,
      FiniteVariationLedgerTasteGate_single_carrier_alignment_round_trip,
      fun _ _ h => FiniteVariationLedgerTasteGate_single_carrier_alignment_toEventFlow_injective h,
      FiniteVariationLedgerTasteGate_single_carrier_alignment_fields,
      rfl⟩

end BEDC.Derived.FiniteVariationLedgerUp
