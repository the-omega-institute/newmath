import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyNullDifferenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyNullDifferenceUp : Type where
  | mk (X Y D Z W T E H K P N : BHist) : CauchyNullDifferenceUp
  deriving DecidableEq

def cauchyNullDifferenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyNullDifferenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyNullDifferenceEncodeBHist h

def cauchyNullDifferenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyNullDifferenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyNullDifferenceDecodeBHist tail)

private theorem CauchyNullDifferenceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cauchyNullDifferenceDecodeBHist (cauchyNullDifferenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyNullDifferenceFields : CauchyNullDifferenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyNullDifferenceUp.mk X Y D Z W T E H K P N =>
      [X, Y, D, Z, W, T, E, H, K, P, N]

def cauchyNullDifferenceToEventFlow : CauchyNullDifferenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyNullDifferenceFields x).map cauchyNullDifferenceEncodeBHist

private def cauchyNullDifferenceEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyNullDifferenceEventAt index rest

def cauchyNullDifferenceFromEventFlow (ef : EventFlow) :
    Option CauchyNullDifferenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyNullDifferenceUp.mk
      (cauchyNullDifferenceDecodeBHist (cauchyNullDifferenceEventAt 0 ef))
      (cauchyNullDifferenceDecodeBHist (cauchyNullDifferenceEventAt 1 ef))
      (cauchyNullDifferenceDecodeBHist (cauchyNullDifferenceEventAt 2 ef))
      (cauchyNullDifferenceDecodeBHist (cauchyNullDifferenceEventAt 3 ef))
      (cauchyNullDifferenceDecodeBHist (cauchyNullDifferenceEventAt 4 ef))
      (cauchyNullDifferenceDecodeBHist (cauchyNullDifferenceEventAt 5 ef))
      (cauchyNullDifferenceDecodeBHist (cauchyNullDifferenceEventAt 6 ef))
      (cauchyNullDifferenceDecodeBHist (cauchyNullDifferenceEventAt 7 ef))
      (cauchyNullDifferenceDecodeBHist (cauchyNullDifferenceEventAt 8 ef))
      (cauchyNullDifferenceDecodeBHist (cauchyNullDifferenceEventAt 9 ef))
      (cauchyNullDifferenceDecodeBHist (cauchyNullDifferenceEventAt 10 ef)))

private theorem CauchyNullDifferenceTasteGate_single_carrier_alignment_round_trip
    (x : CauchyNullDifferenceUp) :
    cauchyNullDifferenceFromEventFlow (cauchyNullDifferenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X Y D Z W T E H K P N =>
      change
        some
          (CauchyNullDifferenceUp.mk
            (cauchyNullDifferenceDecodeBHist (cauchyNullDifferenceEncodeBHist X))
            (cauchyNullDifferenceDecodeBHist (cauchyNullDifferenceEncodeBHist Y))
            (cauchyNullDifferenceDecodeBHist (cauchyNullDifferenceEncodeBHist D))
            (cauchyNullDifferenceDecodeBHist (cauchyNullDifferenceEncodeBHist Z))
            (cauchyNullDifferenceDecodeBHist (cauchyNullDifferenceEncodeBHist W))
            (cauchyNullDifferenceDecodeBHist (cauchyNullDifferenceEncodeBHist T))
            (cauchyNullDifferenceDecodeBHist (cauchyNullDifferenceEncodeBHist E))
            (cauchyNullDifferenceDecodeBHist (cauchyNullDifferenceEncodeBHist H))
            (cauchyNullDifferenceDecodeBHist (cauchyNullDifferenceEncodeBHist K))
            (cauchyNullDifferenceDecodeBHist (cauchyNullDifferenceEncodeBHist P))
            (cauchyNullDifferenceDecodeBHist (cauchyNullDifferenceEncodeBHist N))) =
          some (CauchyNullDifferenceUp.mk X Y D Z W T E H K P N)
      rw [CauchyNullDifferenceTasteGate_single_carrier_alignment_decode_encode X,
        CauchyNullDifferenceTasteGate_single_carrier_alignment_decode_encode Y,
        CauchyNullDifferenceTasteGate_single_carrier_alignment_decode_encode D,
        CauchyNullDifferenceTasteGate_single_carrier_alignment_decode_encode Z,
        CauchyNullDifferenceTasteGate_single_carrier_alignment_decode_encode W,
        CauchyNullDifferenceTasteGate_single_carrier_alignment_decode_encode T,
        CauchyNullDifferenceTasteGate_single_carrier_alignment_decode_encode E,
        CauchyNullDifferenceTasteGate_single_carrier_alignment_decode_encode H,
        CauchyNullDifferenceTasteGate_single_carrier_alignment_decode_encode K,
        CauchyNullDifferenceTasteGate_single_carrier_alignment_decode_encode P,
        CauchyNullDifferenceTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchyNullDifferenceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyNullDifferenceUp} :
    cauchyNullDifferenceToEventFlow x = cauchyNullDifferenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyNullDifferenceFromEventFlow (cauchyNullDifferenceToEventFlow x) =
        cauchyNullDifferenceFromEventFlow (cauchyNullDifferenceToEventFlow y) :=
    congrArg cauchyNullDifferenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyNullDifferenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyNullDifferenceTasteGate_single_carrier_alignment_round_trip y)))

private theorem CauchyNullDifferenceTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : CauchyNullDifferenceUp,
      cauchyNullDifferenceFields x = cauchyNullDifferenceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 Y1 D1 Z1 W1 T1 E1 H1 K1 P1 N1 =>
      cases y with
      | mk X2 Y2 D2 Z2 W2 T2 E2 H2 K2 P2 N2 =>
          cases hfields
          rfl

instance cauchyNullDifferenceBHistCarrier :
    BHistCarrier CauchyNullDifferenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyNullDifferenceToEventFlow
  fromEventFlow := cauchyNullDifferenceFromEventFlow

instance cauchyNullDifferenceChapterTasteGate :
    ChapterTasteGate CauchyNullDifferenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyNullDifferenceFromEventFlow (cauchyNullDifferenceToEventFlow x) = some x
    exact CauchyNullDifferenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyNullDifferenceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance cauchyNullDifferenceFieldFaithful :
    FieldFaithful CauchyNullDifferenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyNullDifferenceFields
  field_faithful := CauchyNullDifferenceTasteGate_single_carrier_alignment_fields_faithful

instance cauchyNullDifferenceNontrivial : Nontrivial CauchyNullDifferenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyNullDifferenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      CauchyNullDifferenceUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def CauchyNullDifferenceTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate CauchyNullDifferenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyNullDifferenceChapterTasteGate

theorem CauchyNullDifferenceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyNullDifferenceDecodeBHist (cauchyNullDifferenceEncodeBHist h) = h) ∧
      (∀ x : CauchyNullDifferenceUp,
        cauchyNullDifferenceFromEventFlow (cauchyNullDifferenceToEventFlow x) = some x) ∧
        (∀ x y : CauchyNullDifferenceUp,
          cauchyNullDifferenceToEventFlow x = cauchyNullDifferenceToEventFlow y →
            x = y) ∧
          cauchyNullDifferenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CauchyNullDifferenceTasteGate_single_carrier_alignment_decode_encode,
      CauchyNullDifferenceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CauchyNullDifferenceTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CauchyNullDifferenceUp
