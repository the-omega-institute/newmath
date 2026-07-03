import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EulerianNumberUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EulerianNumberUp : Type where
  | mk (n k Pi D A R V H C P N : BHist) : EulerianNumberUp
  deriving DecidableEq

def eulerianNumberEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: eulerianNumberEncodeBHist h
  | BHist.e1 h => BMark.b1 :: eulerianNumberEncodeBHist h

def eulerianNumberDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (eulerianNumberDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (eulerianNumberDecodeBHist tail)

private theorem EulerianNumberTasteGate_single_carrier_alignment_decode :
    forall h : BHist, eulerianNumberDecodeBHist (eulerianNumberEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def eulerianNumberFields : EulerianNumberUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | EulerianNumberUp.mk n k Pi D A R V H C P N => [n, k, Pi, D, A, R, V, H, C, P, N]

def eulerianNumberToEventFlow : EulerianNumberUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (eulerianNumberFields x).map eulerianNumberEncodeBHist

private def eulerianNumberEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, event :: _ => event
  | Nat.succ n, _ :: rest => eulerianNumberEventAt n rest
  | _, [] => []

def eulerianNumberFromEventFlow (flow : EventFlow) : Option EulerianNumberUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (EulerianNumberUp.mk
      (eulerianNumberDecodeBHist (eulerianNumberEventAt 0 flow))
      (eulerianNumberDecodeBHist (eulerianNumberEventAt 1 flow))
      (eulerianNumberDecodeBHist (eulerianNumberEventAt 2 flow))
      (eulerianNumberDecodeBHist (eulerianNumberEventAt 3 flow))
      (eulerianNumberDecodeBHist (eulerianNumberEventAt 4 flow))
      (eulerianNumberDecodeBHist (eulerianNumberEventAt 5 flow))
      (eulerianNumberDecodeBHist (eulerianNumberEventAt 6 flow))
      (eulerianNumberDecodeBHist (eulerianNumberEventAt 7 flow))
      (eulerianNumberDecodeBHist (eulerianNumberEventAt 8 flow))
      (eulerianNumberDecodeBHist (eulerianNumberEventAt 9 flow))
      (eulerianNumberDecodeBHist (eulerianNumberEventAt 10 flow)))

private theorem EulerianNumberTasteGate_single_carrier_alignment_round_trip :
    forall x : EulerianNumberUp,
      eulerianNumberFromEventFlow (eulerianNumberToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk n k Pi D A R V H C P N =>
      change
        some
          (EulerianNumberUp.mk
            (eulerianNumberDecodeBHist (eulerianNumberEncodeBHist n))
            (eulerianNumberDecodeBHist (eulerianNumberEncodeBHist k))
            (eulerianNumberDecodeBHist (eulerianNumberEncodeBHist Pi))
            (eulerianNumberDecodeBHist (eulerianNumberEncodeBHist D))
            (eulerianNumberDecodeBHist (eulerianNumberEncodeBHist A))
            (eulerianNumberDecodeBHist (eulerianNumberEncodeBHist R))
            (eulerianNumberDecodeBHist (eulerianNumberEncodeBHist V))
            (eulerianNumberDecodeBHist (eulerianNumberEncodeBHist H))
            (eulerianNumberDecodeBHist (eulerianNumberEncodeBHist C))
            (eulerianNumberDecodeBHist (eulerianNumberEncodeBHist P))
            (eulerianNumberDecodeBHist (eulerianNumberEncodeBHist N))) =
          some (EulerianNumberUp.mk n k Pi D A R V H C P N)
      rw [EulerianNumberTasteGate_single_carrier_alignment_decode n,
        EulerianNumberTasteGate_single_carrier_alignment_decode k,
        EulerianNumberTasteGate_single_carrier_alignment_decode Pi,
        EulerianNumberTasteGate_single_carrier_alignment_decode D,
        EulerianNumberTasteGate_single_carrier_alignment_decode A,
        EulerianNumberTasteGate_single_carrier_alignment_decode R,
        EulerianNumberTasteGate_single_carrier_alignment_decode V,
        EulerianNumberTasteGate_single_carrier_alignment_decode H,
        EulerianNumberTasteGate_single_carrier_alignment_decode C,
        EulerianNumberTasteGate_single_carrier_alignment_decode P,
        EulerianNumberTasteGate_single_carrier_alignment_decode N]

private theorem EulerianNumberTasteGate_single_carrier_alignment_injective
    {x y : EulerianNumberUp} :
    eulerianNumberToEventFlow x = eulerianNumberToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      eulerianNumberFromEventFlow (eulerianNumberToEventFlow x) =
        eulerianNumberFromEventFlow (eulerianNumberToEventFlow y) :=
    congrArg eulerianNumberFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (EulerianNumberTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (EulerianNumberTasteGate_single_carrier_alignment_round_trip y)))

private theorem EulerianNumberTasteGate_single_carrier_alignment_fields :
    forall x y : EulerianNumberUp, eulerianNumberFields x = eulerianNumberFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk n1 k1 Pi1 D1 A1 R1 V1 H1 C1 P1 N1 =>
      cases y with
      | mk n2 k2 Pi2 D2 A2 R2 V2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance eulerianNumberBHistCarrier : BHistCarrier EulerianNumberUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := eulerianNumberToEventFlow
  fromEventFlow := eulerianNumberFromEventFlow

instance eulerianNumberChapterTasteGate : ChapterTasteGate EulerianNumberUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change eulerianNumberFromEventFlow (eulerianNumberToEventFlow x) = some x
    exact EulerianNumberTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (EulerianNumberTasteGate_single_carrier_alignment_injective heq)

instance eulerianNumberFieldFaithful : FieldFaithful EulerianNumberUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := eulerianNumberFields
  field_faithful := EulerianNumberTasteGate_single_carrier_alignment_fields

instance eulerianNumberNontrivial : Nontrivial EulerianNumberUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨EulerianNumberUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      EulerianNumberUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate EulerianNumberUp :=
  -- BEDC touchpoint anchor: BHist BMark
  eulerianNumberChapterTasteGate

theorem EulerianNumberTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate EulerianNumberUp) /\
      Nonempty (FieldFaithful EulerianNumberUp) /\
        Nonempty (Nontrivial EulerianNumberUp) /\
          (forall h : BHist, eulerianNumberDecodeBHist (eulerianNumberEncodeBHist h) = h) /\
            (forall x : EulerianNumberUp,
              eulerianNumberFromEventFlow (eulerianNumberToEventFlow x) = some x) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨eulerianNumberChapterTasteGate⟩,
      ⟨eulerianNumberFieldFaithful⟩,
      ⟨eulerianNumberNontrivial⟩,
      EulerianNumberTasteGate_single_carrier_alignment_decode,
      EulerianNumberTasteGate_single_carrier_alignment_round_trip⟩

end BEDC.Derived.EulerianNumberUp
