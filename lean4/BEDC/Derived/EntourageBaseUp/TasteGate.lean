import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EntourageBaseUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EntourageBaseUp : Type where
  | mk (U M B R W D H C P N : BHist) : EntourageBaseUp

def entourageBaseEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: entourageBaseEncodeBHist h
  | BHist.e1 h => BMark.b1 :: entourageBaseEncodeBHist h

def entourageBaseDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (entourageBaseDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (entourageBaseDecodeBHist tail)

private theorem EntourageBaseTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, entourageBaseDecodeBHist (entourageBaseEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def entourageBaseFields : EntourageBaseUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | EntourageBaseUp.mk U M B R W D H C P N => [U, M, B, R, W, D, H, C, P, N]

def entourageBaseToEventFlow : EntourageBaseUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (entourageBaseFields x).map entourageBaseEncodeBHist

private def entourageBaseEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => entourageBaseEventAtDefault index rest

def entourageBaseFromEventFlow (ef : EventFlow) : Option EntourageBaseUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (EntourageBaseUp.mk
      (entourageBaseDecodeBHist (entourageBaseEventAtDefault 0 ef))
      (entourageBaseDecodeBHist (entourageBaseEventAtDefault 1 ef))
      (entourageBaseDecodeBHist (entourageBaseEventAtDefault 2 ef))
      (entourageBaseDecodeBHist (entourageBaseEventAtDefault 3 ef))
      (entourageBaseDecodeBHist (entourageBaseEventAtDefault 4 ef))
      (entourageBaseDecodeBHist (entourageBaseEventAtDefault 5 ef))
      (entourageBaseDecodeBHist (entourageBaseEventAtDefault 6 ef))
      (entourageBaseDecodeBHist (entourageBaseEventAtDefault 7 ef))
      (entourageBaseDecodeBHist (entourageBaseEventAtDefault 8 ef))
      (entourageBaseDecodeBHist (entourageBaseEventAtDefault 9 ef)))

private theorem EntourageBaseTasteGate_single_carrier_alignment_round_trip :
    ∀ x : EntourageBaseUp,
      entourageBaseFromEventFlow (entourageBaseToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk U M B R W D H C P N =>
      change
        some
          (EntourageBaseUp.mk
            (entourageBaseDecodeBHist (entourageBaseEncodeBHist U))
            (entourageBaseDecodeBHist (entourageBaseEncodeBHist M))
            (entourageBaseDecodeBHist (entourageBaseEncodeBHist B))
            (entourageBaseDecodeBHist (entourageBaseEncodeBHist R))
            (entourageBaseDecodeBHist (entourageBaseEncodeBHist W))
            (entourageBaseDecodeBHist (entourageBaseEncodeBHist D))
            (entourageBaseDecodeBHist (entourageBaseEncodeBHist H))
            (entourageBaseDecodeBHist (entourageBaseEncodeBHist C))
            (entourageBaseDecodeBHist (entourageBaseEncodeBHist P))
            (entourageBaseDecodeBHist (entourageBaseEncodeBHist N))) =
          some (EntourageBaseUp.mk U M B R W D H C P N)
      rw [EntourageBaseTasteGate_single_carrier_alignment_decode U,
        EntourageBaseTasteGate_single_carrier_alignment_decode M,
        EntourageBaseTasteGate_single_carrier_alignment_decode B,
        EntourageBaseTasteGate_single_carrier_alignment_decode R,
        EntourageBaseTasteGate_single_carrier_alignment_decode W,
        EntourageBaseTasteGate_single_carrier_alignment_decode D,
        EntourageBaseTasteGate_single_carrier_alignment_decode H,
        EntourageBaseTasteGate_single_carrier_alignment_decode C,
        EntourageBaseTasteGate_single_carrier_alignment_decode P,
        EntourageBaseTasteGate_single_carrier_alignment_decode N]

private theorem EntourageBaseTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : EntourageBaseUp} :
    entourageBaseToEventFlow x = entourageBaseToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      entourageBaseFromEventFlow (entourageBaseToEventFlow x) =
        entourageBaseFromEventFlow (entourageBaseToEventFlow y) :=
    congrArg entourageBaseFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (EntourageBaseTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (EntourageBaseTasteGate_single_carrier_alignment_round_trip y)))

private theorem EntourageBaseTasteGate_single_carrier_alignment_fields :
    ∀ x y : EntourageBaseUp, entourageBaseFields x = entourageBaseFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk U1 M1 B1 R1 W1 D1 H1 C1 P1 N1 =>
      cases y with
      | mk U2 M2 B2 R2 W2 D2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance entourageBaseBHistCarrier : BHistCarrier EntourageBaseUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := entourageBaseToEventFlow
  fromEventFlow := entourageBaseFromEventFlow

instance entourageBaseChapterTasteGate : ChapterTasteGate EntourageBaseUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change entourageBaseFromEventFlow (entourageBaseToEventFlow x) = some x
    exact EntourageBaseTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (EntourageBaseTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance entourageBaseFieldFaithful : FieldFaithful EntourageBaseUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := entourageBaseFields
  field_faithful := EntourageBaseTasteGate_single_carrier_alignment_fields

instance entourageBaseNontrivial : Nontrivial EntourageBaseUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨EntourageBaseUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      EntourageBaseUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate EntourageBaseUp :=
  -- BEDC touchpoint anchor: BHist BMark
  entourageBaseChapterTasteGate

theorem EntourageBaseTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate EntourageBaseUp) ∧
      Nonempty (FieldFaithful EntourageBaseUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial EntourageBaseUp) ∧
          (∀ h : BHist, entourageBaseDecodeBHist (entourageBaseEncodeBHist h) = h) ∧
            (∀ x : EntourageBaseUp,
              entourageBaseFromEventFlow (entourageBaseToEventFlow x) = some x) ∧
              (∀ x y : EntourageBaseUp,
                entourageBaseToEventFlow x = entourageBaseToEventFlow y → x = y) ∧
                entourageBaseEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨entourageBaseChapterTasteGate⟩,
      ⟨entourageBaseFieldFaithful⟩,
      ⟨entourageBaseNontrivial⟩,
      EntourageBaseTasteGate_single_carrier_alignment_decode,
      EntourageBaseTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => EntourageBaseTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.EntourageBaseUp
