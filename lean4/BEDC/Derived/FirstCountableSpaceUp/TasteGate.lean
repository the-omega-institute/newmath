import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FirstCountableSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FirstCountableSpaceUp : Type where
  | mk (X T M L D S R H C P N : BHist) : FirstCountableSpaceUp
  deriving DecidableEq

def firstCountableSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: firstCountableSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: firstCountableSpaceEncodeBHist h

def firstCountableSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (firstCountableSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (firstCountableSpaceDecodeBHist tail)

private theorem FirstCountableSpaceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, firstCountableSpaceDecodeBHist (firstCountableSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def firstCountableSpaceFields : FirstCountableSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FirstCountableSpaceUp.mk X T M L D S R H C P N => [X, T, M, L, D, S, R, H, C, P, N]

def firstCountableSpaceToEventFlow : FirstCountableSpaceUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (firstCountableSpaceFields x).map firstCountableSpaceEncodeBHist

private def firstCountableSpaceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => firstCountableSpaceEventAtDefault index rest

def firstCountableSpaceFromEventFlow (ef : EventFlow) : Option FirstCountableSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FirstCountableSpaceUp.mk
      (firstCountableSpaceDecodeBHist (firstCountableSpaceEventAtDefault 0 ef))
      (firstCountableSpaceDecodeBHist (firstCountableSpaceEventAtDefault 1 ef))
      (firstCountableSpaceDecodeBHist (firstCountableSpaceEventAtDefault 2 ef))
      (firstCountableSpaceDecodeBHist (firstCountableSpaceEventAtDefault 3 ef))
      (firstCountableSpaceDecodeBHist (firstCountableSpaceEventAtDefault 4 ef))
      (firstCountableSpaceDecodeBHist (firstCountableSpaceEventAtDefault 5 ef))
      (firstCountableSpaceDecodeBHist (firstCountableSpaceEventAtDefault 6 ef))
      (firstCountableSpaceDecodeBHist (firstCountableSpaceEventAtDefault 7 ef))
      (firstCountableSpaceDecodeBHist (firstCountableSpaceEventAtDefault 8 ef))
      (firstCountableSpaceDecodeBHist (firstCountableSpaceEventAtDefault 9 ef))
      (firstCountableSpaceDecodeBHist (firstCountableSpaceEventAtDefault 10 ef)))

private theorem FirstCountableSpaceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : FirstCountableSpaceUp,
      firstCountableSpaceFromEventFlow (firstCountableSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X T M L D S R H C P N =>
      change
        some
          (FirstCountableSpaceUp.mk
            (firstCountableSpaceDecodeBHist (firstCountableSpaceEncodeBHist X))
            (firstCountableSpaceDecodeBHist (firstCountableSpaceEncodeBHist T))
            (firstCountableSpaceDecodeBHist (firstCountableSpaceEncodeBHist M))
            (firstCountableSpaceDecodeBHist (firstCountableSpaceEncodeBHist L))
            (firstCountableSpaceDecodeBHist (firstCountableSpaceEncodeBHist D))
            (firstCountableSpaceDecodeBHist (firstCountableSpaceEncodeBHist S))
            (firstCountableSpaceDecodeBHist (firstCountableSpaceEncodeBHist R))
            (firstCountableSpaceDecodeBHist (firstCountableSpaceEncodeBHist H))
            (firstCountableSpaceDecodeBHist (firstCountableSpaceEncodeBHist C))
            (firstCountableSpaceDecodeBHist (firstCountableSpaceEncodeBHist P))
            (firstCountableSpaceDecodeBHist (firstCountableSpaceEncodeBHist N))) =
          some (FirstCountableSpaceUp.mk X T M L D S R H C P N)
      rw [FirstCountableSpaceTasteGate_single_carrier_alignment_decode X,
        FirstCountableSpaceTasteGate_single_carrier_alignment_decode T,
        FirstCountableSpaceTasteGate_single_carrier_alignment_decode M,
        FirstCountableSpaceTasteGate_single_carrier_alignment_decode L,
        FirstCountableSpaceTasteGate_single_carrier_alignment_decode D,
        FirstCountableSpaceTasteGate_single_carrier_alignment_decode S,
        FirstCountableSpaceTasteGate_single_carrier_alignment_decode R,
        FirstCountableSpaceTasteGate_single_carrier_alignment_decode H,
        FirstCountableSpaceTasteGate_single_carrier_alignment_decode C,
        FirstCountableSpaceTasteGate_single_carrier_alignment_decode P,
        FirstCountableSpaceTasteGate_single_carrier_alignment_decode N]

private theorem FirstCountableSpaceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FirstCountableSpaceUp} :
    firstCountableSpaceToEventFlow x = firstCountableSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      firstCountableSpaceFromEventFlow (firstCountableSpaceToEventFlow x) =
        firstCountableSpaceFromEventFlow (firstCountableSpaceToEventFlow y) :=
    congrArg firstCountableSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (FirstCountableSpaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (FirstCountableSpaceTasteGate_single_carrier_alignment_round_trip y)))

private theorem FirstCountableSpaceTasteGate_single_carrier_alignment_fields :
    ∀ x y : FirstCountableSpaceUp, firstCountableSpaceFields x = firstCountableSpaceFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 T1 M1 L1 D1 S1 R1 H1 C1 P1 N1 =>
      cases y with
      | mk X2 T2 M2 L2 D2 S2 R2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance firstCountableSpaceBHistCarrier : BHistCarrier FirstCountableSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := firstCountableSpaceToEventFlow
  fromEventFlow := firstCountableSpaceFromEventFlow

instance firstCountableSpaceChapterTasteGate : ChapterTasteGate FirstCountableSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change firstCountableSpaceFromEventFlow (firstCountableSpaceToEventFlow x) = some x
    exact FirstCountableSpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FirstCountableSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance firstCountableSpaceFieldFaithful : FieldFaithful FirstCountableSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := firstCountableSpaceFields
  field_faithful := FirstCountableSpaceTasteGate_single_carrier_alignment_fields

def taste_gate : ChapterTasteGate FirstCountableSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  firstCountableSpaceChapterTasteGate

theorem FirstCountableSpaceTasteGate_single_carrier_alignment :
    (∀ h : BHist, firstCountableSpaceDecodeBHist (firstCountableSpaceEncodeBHist h) = h) ∧
      (∀ x : FirstCountableSpaceUp,
        firstCountableSpaceFromEventFlow (firstCountableSpaceToEventFlow x) = some x) ∧
        (∀ x y : FirstCountableSpaceUp,
          firstCountableSpaceToEventFlow x = firstCountableSpaceToEventFlow y → x = y) ∧
          firstCountableSpaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  exact
    ⟨FirstCountableSpaceTasteGate_single_carrier_alignment_decode,
      FirstCountableSpaceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => FirstCountableSpaceTasteGate_single_carrier_alignment_toEventFlow_injective
        heq),
      rfl⟩

end BEDC.Derived.FirstCountableSpaceUp
