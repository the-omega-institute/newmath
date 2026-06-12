import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BoundedRealFamilyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BoundedRealFamilyUp : Type where
  | mk (I W Q R B H C P N : BHist) : BoundedRealFamilyUp
  deriving DecidableEq

def boundedRealFamilyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: boundedRealFamilyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: boundedRealFamilyEncodeBHist h

def boundedRealFamilyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (boundedRealFamilyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (boundedRealFamilyDecodeBHist tail)

private theorem BoundedRealFamilyTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, boundedRealFamilyDecodeBHist (boundedRealFamilyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def boundedRealFamilyFields : BoundedRealFamilyUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BoundedRealFamilyUp.mk I W Q R B H C P N => [I, W, Q, R, B, H, C, P, N]

def boundedRealFamilyToEventFlow : BoundedRealFamilyUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (boundedRealFamilyFields x).map boundedRealFamilyEncodeBHist

private def boundedRealFamilyEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => boundedRealFamilyEventAt index rest

def boundedRealFamilyFromEventFlow (ef : EventFlow) : Option BoundedRealFamilyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BoundedRealFamilyUp.mk
      (boundedRealFamilyDecodeBHist (boundedRealFamilyEventAt 0 ef))
      (boundedRealFamilyDecodeBHist (boundedRealFamilyEventAt 1 ef))
      (boundedRealFamilyDecodeBHist (boundedRealFamilyEventAt 2 ef))
      (boundedRealFamilyDecodeBHist (boundedRealFamilyEventAt 3 ef))
      (boundedRealFamilyDecodeBHist (boundedRealFamilyEventAt 4 ef))
      (boundedRealFamilyDecodeBHist (boundedRealFamilyEventAt 5 ef))
      (boundedRealFamilyDecodeBHist (boundedRealFamilyEventAt 6 ef))
      (boundedRealFamilyDecodeBHist (boundedRealFamilyEventAt 7 ef))
      (boundedRealFamilyDecodeBHist (boundedRealFamilyEventAt 8 ef)))

private theorem BoundedRealFamilyTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BoundedRealFamilyUp,
      boundedRealFamilyFromEventFlow (boundedRealFamilyToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I W Q R B H C P N =>
      change
        some
          (BoundedRealFamilyUp.mk
            (boundedRealFamilyDecodeBHist (boundedRealFamilyEncodeBHist I))
            (boundedRealFamilyDecodeBHist (boundedRealFamilyEncodeBHist W))
            (boundedRealFamilyDecodeBHist (boundedRealFamilyEncodeBHist Q))
            (boundedRealFamilyDecodeBHist (boundedRealFamilyEncodeBHist R))
            (boundedRealFamilyDecodeBHist (boundedRealFamilyEncodeBHist B))
            (boundedRealFamilyDecodeBHist (boundedRealFamilyEncodeBHist H))
            (boundedRealFamilyDecodeBHist (boundedRealFamilyEncodeBHist C))
            (boundedRealFamilyDecodeBHist (boundedRealFamilyEncodeBHist P))
            (boundedRealFamilyDecodeBHist (boundedRealFamilyEncodeBHist N))) =
          some (BoundedRealFamilyUp.mk I W Q R B H C P N)
      rw [BoundedRealFamilyTasteGate_single_carrier_alignment_decode I,
        BoundedRealFamilyTasteGate_single_carrier_alignment_decode W,
        BoundedRealFamilyTasteGate_single_carrier_alignment_decode Q,
        BoundedRealFamilyTasteGate_single_carrier_alignment_decode R,
        BoundedRealFamilyTasteGate_single_carrier_alignment_decode B,
        BoundedRealFamilyTasteGate_single_carrier_alignment_decode H,
        BoundedRealFamilyTasteGate_single_carrier_alignment_decode C,
        BoundedRealFamilyTasteGate_single_carrier_alignment_decode P,
        BoundedRealFamilyTasteGate_single_carrier_alignment_decode N]

private theorem BoundedRealFamilyTasteGate_single_carrier_alignment_injective
    {x y : BoundedRealFamilyUp} :
    boundedRealFamilyToEventFlow x = boundedRealFamilyToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      boundedRealFamilyFromEventFlow (boundedRealFamilyToEventFlow x) =
        boundedRealFamilyFromEventFlow (boundedRealFamilyToEventFlow y) :=
    congrArg boundedRealFamilyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BoundedRealFamilyTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (BoundedRealFamilyTasteGate_single_carrier_alignment_round_trip y)))

private theorem BoundedRealFamilyTasteGate_single_carrier_alignment_fields :
    ∀ x y : BoundedRealFamilyUp, boundedRealFamilyFields x = boundedRealFamilyFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I1 W1 Q1 R1 B1 H1 C1 P1 N1 =>
      cases y with
      | mk I2 W2 Q2 R2 B2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance boundedRealFamilyBHistCarrier : BHistCarrier BoundedRealFamilyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := boundedRealFamilyToEventFlow
  fromEventFlow := boundedRealFamilyFromEventFlow

instance boundedRealFamilyChapterTasteGate : ChapterTasteGate BoundedRealFamilyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change boundedRealFamilyFromEventFlow (boundedRealFamilyToEventFlow x) = some x
    exact BoundedRealFamilyTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BoundedRealFamilyTasteGate_single_carrier_alignment_injective heq)

instance boundedRealFamilyFieldFaithful : FieldFaithful BoundedRealFamilyUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := boundedRealFamilyFields
  field_faithful := BoundedRealFamilyTasteGate_single_carrier_alignment_fields

instance boundedRealFamilyNontrivial : BEDC.Meta.TasteGate.Nontrivial BoundedRealFamilyUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BoundedRealFamilyUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BoundedRealFamilyUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem BoundedRealFamilyTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate BoundedRealFamilyUp) ∧
      Nonempty (FieldFaithful BoundedRealFamilyUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial BoundedRealFamilyUp) ∧
      (∀ h : BHist, boundedRealFamilyDecodeBHist (boundedRealFamilyEncodeBHist h) = h) ∧
      (∀ x : BoundedRealFamilyUp,
        boundedRealFamilyFromEventFlow (boundedRealFamilyToEventFlow x) = some x) ∧
      (∀ x y : BoundedRealFamilyUp,
        boundedRealFamilyToEventFlow x = boundedRealFamilyToEventFlow y → x = y) ∧
      boundedRealFamilyEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨Nonempty.intro boundedRealFamilyChapterTasteGate,
      Nonempty.intro boundedRealFamilyFieldFaithful,
      Nonempty.intro boundedRealFamilyNontrivial,
      BoundedRealFamilyTasteGate_single_carrier_alignment_decode,
      BoundedRealFamilyTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => BoundedRealFamilyTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

end BEDC.Derived.BoundedRealFamilyUp
