import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MeasurableFunctionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MeasurableFunctionUp : Type where
  | mk (S T A B G R H C P N : BHist) : MeasurableFunctionUp
  deriving DecidableEq

def measurableFunctionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: measurableFunctionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: measurableFunctionEncodeBHist h

def measurableFunctionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (measurableFunctionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (measurableFunctionDecodeBHist tail)

private theorem MeasurableFunctionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, measurableFunctionDecodeBHist (measurableFunctionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def measurableFunctionFields : MeasurableFunctionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MeasurableFunctionUp.mk S T A B G R H C P N => [S, T, A, B, G, R, H, C, P, N]

def measurableFunctionToEventFlow : MeasurableFunctionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (measurableFunctionFields x).map measurableFunctionEncodeBHist

private def measurableFunctionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => measurableFunctionEventAtDefault index rest

def measurableFunctionFromEventFlow (ef : EventFlow) : Option MeasurableFunctionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MeasurableFunctionUp.mk
      (measurableFunctionDecodeBHist (measurableFunctionEventAtDefault 0 ef))
      (measurableFunctionDecodeBHist (measurableFunctionEventAtDefault 1 ef))
      (measurableFunctionDecodeBHist (measurableFunctionEventAtDefault 2 ef))
      (measurableFunctionDecodeBHist (measurableFunctionEventAtDefault 3 ef))
      (measurableFunctionDecodeBHist (measurableFunctionEventAtDefault 4 ef))
      (measurableFunctionDecodeBHist (measurableFunctionEventAtDefault 5 ef))
      (measurableFunctionDecodeBHist (measurableFunctionEventAtDefault 6 ef))
      (measurableFunctionDecodeBHist (measurableFunctionEventAtDefault 7 ef))
      (measurableFunctionDecodeBHist (measurableFunctionEventAtDefault 8 ef))
      (measurableFunctionDecodeBHist (measurableFunctionEventAtDefault 9 ef)))

private theorem MeasurableFunctionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : MeasurableFunctionUp,
      measurableFunctionFromEventFlow (measurableFunctionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk S T A B G R H C P N =>
      change
        some
          (MeasurableFunctionUp.mk
            (measurableFunctionDecodeBHist (measurableFunctionEncodeBHist S))
            (measurableFunctionDecodeBHist (measurableFunctionEncodeBHist T))
            (measurableFunctionDecodeBHist (measurableFunctionEncodeBHist A))
            (measurableFunctionDecodeBHist (measurableFunctionEncodeBHist B))
            (measurableFunctionDecodeBHist (measurableFunctionEncodeBHist G))
            (measurableFunctionDecodeBHist (measurableFunctionEncodeBHist R))
            (measurableFunctionDecodeBHist (measurableFunctionEncodeBHist H))
            (measurableFunctionDecodeBHist (measurableFunctionEncodeBHist C))
            (measurableFunctionDecodeBHist (measurableFunctionEncodeBHist P))
            (measurableFunctionDecodeBHist (measurableFunctionEncodeBHist N))) =
          some (MeasurableFunctionUp.mk S T A B G R H C P N)
      rw [MeasurableFunctionTasteGate_single_carrier_alignment_decode S,
        MeasurableFunctionTasteGate_single_carrier_alignment_decode T,
        MeasurableFunctionTasteGate_single_carrier_alignment_decode A,
        MeasurableFunctionTasteGate_single_carrier_alignment_decode B,
        MeasurableFunctionTasteGate_single_carrier_alignment_decode G,
        MeasurableFunctionTasteGate_single_carrier_alignment_decode R,
        MeasurableFunctionTasteGate_single_carrier_alignment_decode H,
        MeasurableFunctionTasteGate_single_carrier_alignment_decode C,
        MeasurableFunctionTasteGate_single_carrier_alignment_decode P,
        MeasurableFunctionTasteGate_single_carrier_alignment_decode N]

private theorem MeasurableFunctionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : MeasurableFunctionUp} :
    measurableFunctionToEventFlow x = measurableFunctionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      measurableFunctionFromEventFlow (measurableFunctionToEventFlow x) =
        measurableFunctionFromEventFlow (measurableFunctionToEventFlow y) :=
    congrArg measurableFunctionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (MeasurableFunctionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (MeasurableFunctionTasteGate_single_carrier_alignment_round_trip y)))

private theorem MeasurableFunctionTasteGate_single_carrier_alignment_fields :
    ∀ x y : MeasurableFunctionUp,
      measurableFunctionFields x = measurableFunctionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 T1 A1 B1 G1 R1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 T2 A2 B2 G2 R2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance measurableFunctionBHistCarrier : BHistCarrier MeasurableFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := measurableFunctionToEventFlow
  fromEventFlow := measurableFunctionFromEventFlow

instance measurableFunctionChapterTasteGate : ChapterTasteGate MeasurableFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change measurableFunctionFromEventFlow (measurableFunctionToEventFlow x) = some x
    exact MeasurableFunctionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (MeasurableFunctionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance measurableFunctionFieldFaithful : FieldFaithful MeasurableFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := measurableFunctionFields
  field_faithful := MeasurableFunctionTasteGate_single_carrier_alignment_fields

instance measurableFunctionNontrivial : Nontrivial MeasurableFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MeasurableFunctionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MeasurableFunctionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MeasurableFunctionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  measurableFunctionChapterTasteGate

theorem MeasurableFunctionTasteGate_single_carrier_alignment :
    (∀ h : BHist, measurableFunctionDecodeBHist (measurableFunctionEncodeBHist h) = h) ∧
      (∀ x : MeasurableFunctionUp,
        measurableFunctionFromEventFlow (measurableFunctionToEventFlow x) = some x) ∧
        (∀ x y : MeasurableFunctionUp,
          measurableFunctionToEventFlow x = measurableFunctionToEventFlow y → x = y) ∧
          measurableFunctionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨MeasurableFunctionTasteGate_single_carrier_alignment_decode,
      MeasurableFunctionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        MeasurableFunctionTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.MeasurableFunctionUp
