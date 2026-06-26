import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteLipschitzFamilyUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteLipschitzFamilyUp : Type where
  | mk (X Y I M L V H C P N : BHist) : FiniteLipschitzFamilyUp
  deriving DecidableEq

def finiteLipschitzFamilyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteLipschitzFamilyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteLipschitzFamilyEncodeBHist h

def finiteLipschitzFamilyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteLipschitzFamilyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteLipschitzFamilyDecodeBHist tail)

private theorem FiniteLipschitzFamilyTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      finiteLipschitzFamilyDecodeBHist (finiteLipschitzFamilyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteLipschitzFamilyFields : FiniteLipschitzFamilyUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteLipschitzFamilyUp.mk X Y I M L V H C P N => [X, Y, I, M, L, V, H, C, P, N]

def finiteLipschitzFamilyToEventFlow : FiniteLipschitzFamilyUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (finiteLipschitzFamilyFields x).map finiteLipschitzFamilyEncodeBHist

private def finiteLipschitzFamilyEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => finiteLipschitzFamilyEventAtDefault index rest

def finiteLipschitzFamilyFromEventFlow (ef : EventFlow) : Option FiniteLipschitzFamilyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FiniteLipschitzFamilyUp.mk
      (finiteLipschitzFamilyDecodeBHist (finiteLipschitzFamilyEventAtDefault 0 ef))
      (finiteLipschitzFamilyDecodeBHist (finiteLipschitzFamilyEventAtDefault 1 ef))
      (finiteLipschitzFamilyDecodeBHist (finiteLipschitzFamilyEventAtDefault 2 ef))
      (finiteLipschitzFamilyDecodeBHist (finiteLipschitzFamilyEventAtDefault 3 ef))
      (finiteLipschitzFamilyDecodeBHist (finiteLipschitzFamilyEventAtDefault 4 ef))
      (finiteLipschitzFamilyDecodeBHist (finiteLipschitzFamilyEventAtDefault 5 ef))
      (finiteLipschitzFamilyDecodeBHist (finiteLipschitzFamilyEventAtDefault 6 ef))
      (finiteLipschitzFamilyDecodeBHist (finiteLipschitzFamilyEventAtDefault 7 ef))
      (finiteLipschitzFamilyDecodeBHist (finiteLipschitzFamilyEventAtDefault 8 ef))
      (finiteLipschitzFamilyDecodeBHist (finiteLipschitzFamilyEventAtDefault 9 ef)))

private theorem FiniteLipschitzFamilyTasteGate_single_carrier_alignment_round_trip :
    ∀ x : FiniteLipschitzFamilyUp,
      finiteLipschitzFamilyFromEventFlow (finiteLipschitzFamilyToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Y I M L V H C P N =>
      change
        some
          (FiniteLipschitzFamilyUp.mk
            (finiteLipschitzFamilyDecodeBHist (finiteLipschitzFamilyEncodeBHist X))
            (finiteLipschitzFamilyDecodeBHist (finiteLipschitzFamilyEncodeBHist Y))
            (finiteLipschitzFamilyDecodeBHist (finiteLipschitzFamilyEncodeBHist I))
            (finiteLipschitzFamilyDecodeBHist (finiteLipschitzFamilyEncodeBHist M))
            (finiteLipschitzFamilyDecodeBHist (finiteLipschitzFamilyEncodeBHist L))
            (finiteLipschitzFamilyDecodeBHist (finiteLipschitzFamilyEncodeBHist V))
            (finiteLipschitzFamilyDecodeBHist (finiteLipschitzFamilyEncodeBHist H))
            (finiteLipschitzFamilyDecodeBHist (finiteLipschitzFamilyEncodeBHist C))
            (finiteLipschitzFamilyDecodeBHist (finiteLipschitzFamilyEncodeBHist P))
            (finiteLipschitzFamilyDecodeBHist (finiteLipschitzFamilyEncodeBHist N))) =
          some (FiniteLipschitzFamilyUp.mk X Y I M L V H C P N)
      rw [FiniteLipschitzFamilyTasteGate_single_carrier_alignment_decode X,
        FiniteLipschitzFamilyTasteGate_single_carrier_alignment_decode Y,
        FiniteLipschitzFamilyTasteGate_single_carrier_alignment_decode I,
        FiniteLipschitzFamilyTasteGate_single_carrier_alignment_decode M,
        FiniteLipschitzFamilyTasteGate_single_carrier_alignment_decode L,
        FiniteLipschitzFamilyTasteGate_single_carrier_alignment_decode V,
        FiniteLipschitzFamilyTasteGate_single_carrier_alignment_decode H,
        FiniteLipschitzFamilyTasteGate_single_carrier_alignment_decode C,
        FiniteLipschitzFamilyTasteGate_single_carrier_alignment_decode P,
        FiniteLipschitzFamilyTasteGate_single_carrier_alignment_decode N]

private theorem FiniteLipschitzFamilyToEventFlow_injective {x y : FiniteLipschitzFamilyUp} :
    finiteLipschitzFamilyToEventFlow x = finiteLipschitzFamilyToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteLipschitzFamilyFromEventFlow (finiteLipschitzFamilyToEventFlow x) =
        finiteLipschitzFamilyFromEventFlow (finiteLipschitzFamilyToEventFlow y) :=
    congrArg finiteLipschitzFamilyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (FiniteLipschitzFamilyTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (FiniteLipschitzFamilyTasteGate_single_carrier_alignment_round_trip y)))

private theorem FiniteLipschitzFamilyTasteGate_single_carrier_alignment_fields :
    ∀ x y : FiniteLipschitzFamilyUp,
      finiteLipschitzFamilyFields x = finiteLipschitzFamilyFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 Y1 I1 M1 L1 V1 H1 C1 P1 N1 =>
      cases y with
      | mk X2 Y2 I2 M2 L2 V2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance finiteLipschitzFamilyBHistCarrier : BHistCarrier FiniteLipschitzFamilyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteLipschitzFamilyToEventFlow
  fromEventFlow := finiteLipschitzFamilyFromEventFlow

instance finiteLipschitzFamilyChapterTasteGate : ChapterTasteGate FiniteLipschitzFamilyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteLipschitzFamilyFromEventFlow (finiteLipschitzFamilyToEventFlow x) = some x
    exact FiniteLipschitzFamilyTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FiniteLipschitzFamilyToEventFlow_injective heq)

instance finiteLipschitzFamilyFieldFaithful : FieldFaithful FiniteLipschitzFamilyUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteLipschitzFamilyFields
  field_faithful := FiniteLipschitzFamilyTasteGate_single_carrier_alignment_fields

instance finiteLipschitzFamilyNontrivial : Nontrivial FiniteLipschitzFamilyUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteLipschitzFamilyUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FiniteLipschitzFamilyUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem FiniteLipschitzFamilyTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate FiniteLipschitzFamilyUp) ∧
      Nonempty (FieldFaithful FiniteLipschitzFamilyUp) ∧
        Nonempty (Nontrivial FiniteLipschitzFamilyUp) ∧
          (∀ h : BHist,
            finiteLipschitzFamilyDecodeBHist (finiteLipschitzFamilyEncodeBHist h) = h) ∧
            finiteLipschitzFamilyEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨finiteLipschitzFamilyChapterTasteGate⟩,
      ⟨finiteLipschitzFamilyFieldFaithful⟩,
      ⟨finiteLipschitzFamilyNontrivial⟩,
      FiniteLipschitzFamilyTasteGate_single_carrier_alignment_decode,
      rfl⟩

end BEDC.Derived.FiniteLipschitzFamilyUp.TasteGate
