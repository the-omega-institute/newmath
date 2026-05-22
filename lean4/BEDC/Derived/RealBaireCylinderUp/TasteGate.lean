import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealBaireCylinderUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealBaireCylinderUp : Type where
  | mk (B S Q E H C P N : BHist) : RealBaireCylinderUp
  deriving DecidableEq

def realBaireCylinderEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realBaireCylinderEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realBaireCylinderEncodeBHist h

def realBaireCylinderDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realBaireCylinderDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realBaireCylinderDecodeBHist tail)

private theorem RealBaireCylinderTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, realBaireCylinderDecodeBHist (realBaireCylinderEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realBaireCylinderFields : RealBaireCylinderUp → List BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | RealBaireCylinderUp.mk baire stream readback real transport replay provenance localName =>
      [baire, stream, readback, real, transport, replay, provenance, localName]

def realBaireCylinderToEventFlow : RealBaireCylinderUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | RealBaireCylinderUp.mk baire stream readback real transport replay provenance localName =>
      [realBaireCylinderEncodeBHist baire, realBaireCylinderEncodeBHist stream,
        realBaireCylinderEncodeBHist readback, realBaireCylinderEncodeBHist real,
        realBaireCylinderEncodeBHist transport, realBaireCylinderEncodeBHist replay,
        realBaireCylinderEncodeBHist provenance, realBaireCylinderEncodeBHist localName]

private def realBaireCylinderEventAt : Nat → EventFlow → RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realBaireCylinderEventAt index rest

def realBaireCylinderFromEventFlow : EventFlow → Option RealBaireCylinderUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (RealBaireCylinderUp.mk
        (realBaireCylinderDecodeBHist (realBaireCylinderEventAt 0 ef))
        (realBaireCylinderDecodeBHist (realBaireCylinderEventAt 1 ef))
        (realBaireCylinderDecodeBHist (realBaireCylinderEventAt 2 ef))
        (realBaireCylinderDecodeBHist (realBaireCylinderEventAt 3 ef))
        (realBaireCylinderDecodeBHist (realBaireCylinderEventAt 4 ef))
        (realBaireCylinderDecodeBHist (realBaireCylinderEventAt 5 ef))
        (realBaireCylinderDecodeBHist (realBaireCylinderEventAt 6 ef))
        (realBaireCylinderDecodeBHist (realBaireCylinderEventAt 7 ef)))

private theorem RealBaireCylinderTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RealBaireCylinderUp,
      realBaireCylinderFromEventFlow (realBaireCylinderToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk baire stream readback real transport replay provenance localName =>
      change
        some
            (RealBaireCylinderUp.mk
              (realBaireCylinderDecodeBHist (realBaireCylinderEncodeBHist baire))
              (realBaireCylinderDecodeBHist (realBaireCylinderEncodeBHist stream))
              (realBaireCylinderDecodeBHist (realBaireCylinderEncodeBHist readback))
              (realBaireCylinderDecodeBHist (realBaireCylinderEncodeBHist real))
              (realBaireCylinderDecodeBHist (realBaireCylinderEncodeBHist transport))
              (realBaireCylinderDecodeBHist (realBaireCylinderEncodeBHist replay))
              (realBaireCylinderDecodeBHist (realBaireCylinderEncodeBHist provenance))
              (realBaireCylinderDecodeBHist (realBaireCylinderEncodeBHist localName))) =
          some
            (RealBaireCylinderUp.mk baire stream readback real transport replay provenance
              localName)
      rw [RealBaireCylinderTasteGate_single_carrier_alignment_decode baire,
        RealBaireCylinderTasteGate_single_carrier_alignment_decode stream,
        RealBaireCylinderTasteGate_single_carrier_alignment_decode readback,
        RealBaireCylinderTasteGate_single_carrier_alignment_decode real,
        RealBaireCylinderTasteGate_single_carrier_alignment_decode transport,
        RealBaireCylinderTasteGate_single_carrier_alignment_decode replay,
        RealBaireCylinderTasteGate_single_carrier_alignment_decode provenance,
        RealBaireCylinderTasteGate_single_carrier_alignment_decode localName]

private theorem RealBaireCylinderTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RealBaireCylinderUp} :
    realBaireCylinderToEventFlow x = realBaireCylinderToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have hsome : some x = some y := by
    calc
      some x = realBaireCylinderFromEventFlow (realBaireCylinderToEventFlow x) :=
        (RealBaireCylinderTasteGate_single_carrier_alignment_round_trip x).symm
      _ = realBaireCylinderFromEventFlow (realBaireCylinderToEventFlow y) :=
        congrArg realBaireCylinderFromEventFlow hxy
      _ = some y := RealBaireCylinderTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj hsome

private theorem RealBaireCylinderTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : RealBaireCylinderUp, realBaireCylinderFields x = realBaireCylinderFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk B1 S1 Q1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk B2 S2 Q2 E2 H2 C2 P2 N2 =>
          injection hfields with hB tail0
          injection tail0 with hS tail1
          injection tail1 with hQ tail2
          injection tail2 with hE tail3
          injection tail3 with hH tail4
          injection tail4 with hC tail5
          injection tail5 with hP tail6
          injection tail6 with hN _
          subst hB
          subst hS
          subst hQ
          subst hE
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance realBaireCylinderBHistCarrier : BHistCarrier RealBaireCylinderUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realBaireCylinderToEventFlow
  fromEventFlow := realBaireCylinderFromEventFlow

instance realBaireCylinderChapterTasteGate : ChapterTasteGate RealBaireCylinderUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realBaireCylinderFromEventFlow (realBaireCylinderToEventFlow x) = some x
    exact RealBaireCylinderTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RealBaireCylinderTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance realBaireCylinderFieldFaithful : FieldFaithful RealBaireCylinderUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realBaireCylinderFields
  field_faithful := RealBaireCylinderTasteGate_single_carrier_alignment_field_faithful

instance realBaireCylinderNontrivial : Nontrivial RealBaireCylinderUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealBaireCylinderUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      RealBaireCylinderUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem RealBaireCylinderTasteGate_single_carrier_alignment :
    (∀ h : BHist, realBaireCylinderDecodeBHist (realBaireCylinderEncodeBHist h) = h) ∧
      (∀ x : RealBaireCylinderUp,
        realBaireCylinderFromEventFlow (realBaireCylinderToEventFlow x) = some x) ∧
      (∀ x y : RealBaireCylinderUp,
        realBaireCylinderToEventFlow x = realBaireCylinderToEventFlow y → x = y) ∧
      realBaireCylinderEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨RealBaireCylinderTasteGate_single_carrier_alignment_decode,
      RealBaireCylinderTasteGate_single_carrier_alignment_round_trip,
      fun _ _ hxy => RealBaireCylinderTasteGate_single_carrier_alignment_toEventFlow_injective hxy,
      rfl⟩

end BEDC.Derived.RealBaireCylinderUp
