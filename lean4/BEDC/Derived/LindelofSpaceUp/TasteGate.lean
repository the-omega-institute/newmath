import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LindelofSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LindelofSpaceUp : Type where
  | mk (X T B U S R H C P N : BHist) : LindelofSpaceUp
  deriving DecidableEq

def lindelofSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: lindelofSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: lindelofSpaceEncodeBHist h

def lindelofSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (lindelofSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (lindelofSpaceDecodeBHist tail)

private theorem LindelofSpaceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, lindelofSpaceDecodeBHist (lindelofSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def lindelofSpaceFields : LindelofSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LindelofSpaceUp.mk X T B U S R H C P N => [X, T, B, U, S, R, H, C, P, N]

def lindelofSpaceToEventFlow : LindelofSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (lindelofSpaceFields x).map lindelofSpaceEncodeBHist

private def lindelofSpaceEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => lindelofSpaceEventAt index rest

def lindelofSpaceFromEventFlow (ef : EventFlow) : Option LindelofSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LindelofSpaceUp.mk
      (lindelofSpaceDecodeBHist (lindelofSpaceEventAt 0 ef))
      (lindelofSpaceDecodeBHist (lindelofSpaceEventAt 1 ef))
      (lindelofSpaceDecodeBHist (lindelofSpaceEventAt 2 ef))
      (lindelofSpaceDecodeBHist (lindelofSpaceEventAt 3 ef))
      (lindelofSpaceDecodeBHist (lindelofSpaceEventAt 4 ef))
      (lindelofSpaceDecodeBHist (lindelofSpaceEventAt 5 ef))
      (lindelofSpaceDecodeBHist (lindelofSpaceEventAt 6 ef))
      (lindelofSpaceDecodeBHist (lindelofSpaceEventAt 7 ef))
      (lindelofSpaceDecodeBHist (lindelofSpaceEventAt 8 ef))
      (lindelofSpaceDecodeBHist (lindelofSpaceEventAt 9 ef)))

private theorem LindelofSpaceTasteGate_single_carrier_alignment_round_trip
    (x : LindelofSpaceUp) :
    lindelofSpaceFromEventFlow (lindelofSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X T B U S R H C P N =>
      change
        some
          (LindelofSpaceUp.mk
            (lindelofSpaceDecodeBHist (lindelofSpaceEncodeBHist X))
            (lindelofSpaceDecodeBHist (lindelofSpaceEncodeBHist T))
            (lindelofSpaceDecodeBHist (lindelofSpaceEncodeBHist B))
            (lindelofSpaceDecodeBHist (lindelofSpaceEncodeBHist U))
            (lindelofSpaceDecodeBHist (lindelofSpaceEncodeBHist S))
            (lindelofSpaceDecodeBHist (lindelofSpaceEncodeBHist R))
            (lindelofSpaceDecodeBHist (lindelofSpaceEncodeBHist H))
            (lindelofSpaceDecodeBHist (lindelofSpaceEncodeBHist C))
            (lindelofSpaceDecodeBHist (lindelofSpaceEncodeBHist P))
            (lindelofSpaceDecodeBHist (lindelofSpaceEncodeBHist N))) =
          some (LindelofSpaceUp.mk X T B U S R H C P N)
      rw [LindelofSpaceTasteGate_single_carrier_alignment_decode X,
        LindelofSpaceTasteGate_single_carrier_alignment_decode T,
        LindelofSpaceTasteGate_single_carrier_alignment_decode B,
        LindelofSpaceTasteGate_single_carrier_alignment_decode U,
        LindelofSpaceTasteGate_single_carrier_alignment_decode S,
        LindelofSpaceTasteGate_single_carrier_alignment_decode R,
        LindelofSpaceTasteGate_single_carrier_alignment_decode H,
        LindelofSpaceTasteGate_single_carrier_alignment_decode C,
        LindelofSpaceTasteGate_single_carrier_alignment_decode P,
        LindelofSpaceTasteGate_single_carrier_alignment_decode N]

private theorem LindelofSpaceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LindelofSpaceUp} :
    lindelofSpaceToEventFlow x = lindelofSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      lindelofSpaceFromEventFlow (lindelofSpaceToEventFlow x) =
        lindelofSpaceFromEventFlow (lindelofSpaceToEventFlow y) :=
    congrArg lindelofSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (LindelofSpaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (LindelofSpaceTasteGate_single_carrier_alignment_round_trip y)))

private theorem lindelofSpace_field_faithful :
    ∀ x y : LindelofSpaceUp, lindelofSpaceFields x = lindelofSpaceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 T1 B1 U1 S1 R1 H1 C1 P1 N1 =>
      cases y with
      | mk X2 T2 B2 U2 S2 R2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance lindelofSpaceBHistCarrier : BHistCarrier LindelofSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := lindelofSpaceToEventFlow
  fromEventFlow := lindelofSpaceFromEventFlow

instance lindelofSpaceChapterTasteGate : ChapterTasteGate LindelofSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change lindelofSpaceFromEventFlow (lindelofSpaceToEventFlow x) = some x
    exact LindelofSpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LindelofSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance lindelofSpaceFieldFaithful : FieldFaithful LindelofSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := lindelofSpaceFields
  field_faithful := lindelofSpace_field_faithful

instance lindelofSpaceNontrivial : Nontrivial LindelofSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LindelofSpaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LindelofSpaceUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate LindelofSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  lindelofSpaceChapterTasteGate

theorem LindelofSpaceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      lindelofSpaceEncodeBHist (BHist.e0 h) = BMark.b0 :: lindelofSpaceEncodeBHist h) ∧
      (∀ h : BHist, lindelofSpaceDecodeBHist (lindelofSpaceEncodeBHist h) = h) ∧
        (∀ x : LindelofSpaceUp,
          lindelofSpaceFromEventFlow (lindelofSpaceToEventFlow x) = some x) ∧
          (∀ x y : LindelofSpaceUp,
            lindelofSpaceToEventFlow x = lindelofSpaceToEventFlow y → x = y) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨by
      intro h
      rfl,
    LindelofSpaceTasteGate_single_carrier_alignment_decode,
    LindelofSpaceTasteGate_single_carrier_alignment_round_trip,
    by
      intro x y heq
      exact LindelofSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq⟩

end BEDC.Derived.LindelofSpaceUp
