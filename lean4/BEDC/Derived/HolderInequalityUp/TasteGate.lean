import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HolderInequalityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HolderInequalityUp : Type where
  | mk (X Y W A B C D E F H T P N : BHist) : HolderInequalityUp
  deriving DecidableEq

def holderInequalityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: holderInequalityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: holderInequalityEncodeBHist h

def holderInequalityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (holderInequalityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (holderInequalityDecodeBHist tail)

private theorem HolderInequalityTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, holderInequalityDecodeBHist (holderInequalityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def holderInequalityFields : HolderInequalityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HolderInequalityUp.mk X Y W A B C D E F H T P N =>
      [X, Y, W, A, B, C, D, E, F, H, T, P, N]

def holderInequalityToEventFlow : HolderInequalityUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (holderInequalityFields x).map holderInequalityEncodeBHist

private def holderInequalityEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => holderInequalityEventAtDefault index rest

def holderInequalityFromEventFlow (ef : EventFlow) : Option HolderInequalityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HolderInequalityUp.mk
      (holderInequalityDecodeBHist (holderInequalityEventAtDefault 0 ef))
      (holderInequalityDecodeBHist (holderInequalityEventAtDefault 1 ef))
      (holderInequalityDecodeBHist (holderInequalityEventAtDefault 2 ef))
      (holderInequalityDecodeBHist (holderInequalityEventAtDefault 3 ef))
      (holderInequalityDecodeBHist (holderInequalityEventAtDefault 4 ef))
      (holderInequalityDecodeBHist (holderInequalityEventAtDefault 5 ef))
      (holderInequalityDecodeBHist (holderInequalityEventAtDefault 6 ef))
      (holderInequalityDecodeBHist (holderInequalityEventAtDefault 7 ef))
      (holderInequalityDecodeBHist (holderInequalityEventAtDefault 8 ef))
      (holderInequalityDecodeBHist (holderInequalityEventAtDefault 9 ef))
      (holderInequalityDecodeBHist (holderInequalityEventAtDefault 10 ef))
      (holderInequalityDecodeBHist (holderInequalityEventAtDefault 11 ef))
      (holderInequalityDecodeBHist (holderInequalityEventAtDefault 12 ef)))

private theorem HolderInequalityTasteGate_single_carrier_alignment_round_trip :
    ∀ x : HolderInequalityUp,
      holderInequalityFromEventFlow (holderInequalityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Y W A B C D E F H T P N =>
      change
        some
          (HolderInequalityUp.mk
            (holderInequalityDecodeBHist (holderInequalityEncodeBHist X))
            (holderInequalityDecodeBHist (holderInequalityEncodeBHist Y))
            (holderInequalityDecodeBHist (holderInequalityEncodeBHist W))
            (holderInequalityDecodeBHist (holderInequalityEncodeBHist A))
            (holderInequalityDecodeBHist (holderInequalityEncodeBHist B))
            (holderInequalityDecodeBHist (holderInequalityEncodeBHist C))
            (holderInequalityDecodeBHist (holderInequalityEncodeBHist D))
            (holderInequalityDecodeBHist (holderInequalityEncodeBHist E))
            (holderInequalityDecodeBHist (holderInequalityEncodeBHist F))
            (holderInequalityDecodeBHist (holderInequalityEncodeBHist H))
            (holderInequalityDecodeBHist (holderInequalityEncodeBHist T))
            (holderInequalityDecodeBHist (holderInequalityEncodeBHist P))
            (holderInequalityDecodeBHist (holderInequalityEncodeBHist N))) =
          some (HolderInequalityUp.mk X Y W A B C D E F H T P N)
      rw [HolderInequalityTasteGate_single_carrier_alignment_decode X,
        HolderInequalityTasteGate_single_carrier_alignment_decode Y,
        HolderInequalityTasteGate_single_carrier_alignment_decode W,
        HolderInequalityTasteGate_single_carrier_alignment_decode A,
        HolderInequalityTasteGate_single_carrier_alignment_decode B,
        HolderInequalityTasteGate_single_carrier_alignment_decode C,
        HolderInequalityTasteGate_single_carrier_alignment_decode D,
        HolderInequalityTasteGate_single_carrier_alignment_decode E,
        HolderInequalityTasteGate_single_carrier_alignment_decode F,
        HolderInequalityTasteGate_single_carrier_alignment_decode H,
        HolderInequalityTasteGate_single_carrier_alignment_decode T,
        HolderInequalityTasteGate_single_carrier_alignment_decode P,
        HolderInequalityTasteGate_single_carrier_alignment_decode N]

private theorem HolderInequalityTasteGate_single_carrier_alignment_injective
    {x y : HolderInequalityUp} :
    holderInequalityToEventFlow x = holderInequalityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      holderInequalityFromEventFlow (holderInequalityToEventFlow x) =
        holderInequalityFromEventFlow (holderInequalityToEventFlow y) :=
    congrArg holderInequalityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (HolderInequalityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (HolderInequalityTasteGate_single_carrier_alignment_round_trip y)))

private theorem HolderInequalityTasteGate_single_carrier_alignment_fields :
    ∀ x y : HolderInequalityUp,
      holderInequalityFields x = holderInequalityFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 Y1 W1 A1 B1 C1 D1 E1 F1 H1 T1 P1 N1 =>
      cases y with
      | mk X2 Y2 W2 A2 B2 C2 D2 E2 F2 H2 T2 P2 N2 =>
          cases hfields
          rfl

instance holderInequalityBHistCarrier : BHistCarrier HolderInequalityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := holderInequalityToEventFlow
  fromEventFlow := holderInequalityFromEventFlow

instance holderInequalityChapterTasteGate : ChapterTasteGate HolderInequalityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change holderInequalityFromEventFlow (holderInequalityToEventFlow x) = some x
    exact HolderInequalityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (HolderInequalityTasteGate_single_carrier_alignment_injective heq)

instance holderInequalityFieldFaithful : FieldFaithful HolderInequalityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := holderInequalityFields
  field_faithful := HolderInequalityTasteGate_single_carrier_alignment_fields

instance holderInequalityNontrivial : Nontrivial HolderInequalityUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨HolderInequalityUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      HolderInequalityUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate HolderInequalityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  holderInequalityChapterTasteGate

theorem HolderInequalityTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate HolderInequalityUp) ∧
      Nonempty (FieldFaithful HolderInequalityUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial HolderInequalityUp) ∧
          (∀ h : BHist,
            holderInequalityDecodeBHist (holderInequalityEncodeBHist h) = h) ∧
            (∀ x : HolderInequalityUp,
              holderInequalityFromEventFlow (holderInequalityToEventFlow x) =
                some x) ∧
              (∀ x y : HolderInequalityUp,
                holderInequalityToEventFlow x = holderInequalityToEventFlow y →
                  x = y) ∧
                holderInequalityEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨Nonempty.intro holderInequalityChapterTasteGate,
      Nonempty.intro holderInequalityFieldFaithful,
      Nonempty.intro holderInequalityNontrivial,
      HolderInequalityTasteGate_single_carrier_alignment_decode,
      HolderInequalityTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => HolderInequalityTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

end BEDC.Derived.HolderInequalityUp
