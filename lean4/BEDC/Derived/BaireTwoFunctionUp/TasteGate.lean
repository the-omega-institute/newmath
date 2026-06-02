import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BaireTwoFunctionUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BaireTwoFunctionUp : Type where
  | mk (B A S Q R H C P N : BHist) : BaireTwoFunctionUp
  deriving DecidableEq

def baireTwoFunctionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: baireTwoFunctionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: baireTwoFunctionEncodeBHist h

def baireTwoFunctionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (baireTwoFunctionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (baireTwoFunctionDecodeBHist tail)

private theorem BaireTwoFunctionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, baireTwoFunctionDecodeBHist (baireTwoFunctionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def baireTwoFunctionFields : BaireTwoFunctionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BaireTwoFunctionUp.mk B A S Q R H C P N => [B, A, S, Q, R, H, C, P, N]

def baireTwoFunctionToEventFlow : BaireTwoFunctionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (baireTwoFunctionFields x).map baireTwoFunctionEncodeBHist

private def baireTwoFunctionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => baireTwoFunctionEventAt index rest

def baireTwoFunctionFromEventFlow (ef : EventFlow) : Option BaireTwoFunctionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BaireTwoFunctionUp.mk
      (baireTwoFunctionDecodeBHist (baireTwoFunctionEventAt 0 ef))
      (baireTwoFunctionDecodeBHist (baireTwoFunctionEventAt 1 ef))
      (baireTwoFunctionDecodeBHist (baireTwoFunctionEventAt 2 ef))
      (baireTwoFunctionDecodeBHist (baireTwoFunctionEventAt 3 ef))
      (baireTwoFunctionDecodeBHist (baireTwoFunctionEventAt 4 ef))
      (baireTwoFunctionDecodeBHist (baireTwoFunctionEventAt 5 ef))
      (baireTwoFunctionDecodeBHist (baireTwoFunctionEventAt 6 ef))
      (baireTwoFunctionDecodeBHist (baireTwoFunctionEventAt 7 ef))
      (baireTwoFunctionDecodeBHist (baireTwoFunctionEventAt 8 ef)))

private theorem BaireTwoFunctionTasteGate_single_carrier_alignment_round_trip
    (x : BaireTwoFunctionUp) :
    baireTwoFunctionFromEventFlow (baireTwoFunctionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk B A S Q R H C P N =>
      change
        some
          (BaireTwoFunctionUp.mk
            (baireTwoFunctionDecodeBHist (baireTwoFunctionEncodeBHist B))
            (baireTwoFunctionDecodeBHist (baireTwoFunctionEncodeBHist A))
            (baireTwoFunctionDecodeBHist (baireTwoFunctionEncodeBHist S))
            (baireTwoFunctionDecodeBHist (baireTwoFunctionEncodeBHist Q))
            (baireTwoFunctionDecodeBHist (baireTwoFunctionEncodeBHist R))
            (baireTwoFunctionDecodeBHist (baireTwoFunctionEncodeBHist H))
            (baireTwoFunctionDecodeBHist (baireTwoFunctionEncodeBHist C))
            (baireTwoFunctionDecodeBHist (baireTwoFunctionEncodeBHist P))
            (baireTwoFunctionDecodeBHist (baireTwoFunctionEncodeBHist N))) =
          some (BaireTwoFunctionUp.mk B A S Q R H C P N)
      rw [BaireTwoFunctionTasteGate_single_carrier_alignment_decode B,
        BaireTwoFunctionTasteGate_single_carrier_alignment_decode A,
        BaireTwoFunctionTasteGate_single_carrier_alignment_decode S,
        BaireTwoFunctionTasteGate_single_carrier_alignment_decode Q,
        BaireTwoFunctionTasteGate_single_carrier_alignment_decode R,
        BaireTwoFunctionTasteGate_single_carrier_alignment_decode H,
        BaireTwoFunctionTasteGate_single_carrier_alignment_decode C,
        BaireTwoFunctionTasteGate_single_carrier_alignment_decode P,
        BaireTwoFunctionTasteGate_single_carrier_alignment_decode N]

private theorem BaireTwoFunctionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BaireTwoFunctionUp} :
    baireTwoFunctionToEventFlow x = baireTwoFunctionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      baireTwoFunctionFromEventFlow (baireTwoFunctionToEventFlow x) =
        baireTwoFunctionFromEventFlow (baireTwoFunctionToEventFlow y) :=
    congrArg baireTwoFunctionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BaireTwoFunctionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (BaireTwoFunctionTasteGate_single_carrier_alignment_round_trip y)))

private theorem BaireTwoFunctionTasteGate_single_carrier_alignment_fields :
    ∀ x y : BaireTwoFunctionUp,
      baireTwoFunctionFields x = baireTwoFunctionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk B1 A1 S1 Q1 R1 H1 C1 P1 N1 =>
      cases y with
      | mk B2 A2 S2 Q2 R2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance baireTwoFunctionBHistCarrier : BHistCarrier BaireTwoFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := baireTwoFunctionToEventFlow
  fromEventFlow := baireTwoFunctionFromEventFlow

instance baireTwoFunctionChapterTasteGate : ChapterTasteGate BaireTwoFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change baireTwoFunctionFromEventFlow (baireTwoFunctionToEventFlow x) = some x
    exact BaireTwoFunctionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BaireTwoFunctionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance baireTwoFunctionFieldFaithful : FieldFaithful BaireTwoFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := baireTwoFunctionFields
  field_faithful := BaireTwoFunctionTasteGate_single_carrier_alignment_fields

instance baireTwoFunctionNontrivial :
    BEDC.Meta.TasteGate.Nontrivial BaireTwoFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BaireTwoFunctionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BaireTwoFunctionUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem BaireTwoFunctionTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate BaireTwoFunctionUp) ∧
      Nonempty (FieldFaithful BaireTwoFunctionUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial BaireTwoFunctionUp) ∧
      (∀ h : BHist, baireTwoFunctionDecodeBHist (baireTwoFunctionEncodeBHist h) = h) ∧
      (∀ x : BaireTwoFunctionUp,
        baireTwoFunctionFromEventFlow (baireTwoFunctionToEventFlow x) = some x) ∧
      (∀ x y : BaireTwoFunctionUp,
        baireTwoFunctionToEventFlow x = baireTwoFunctionToEventFlow y → x = y) ∧
      baireTwoFunctionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨baireTwoFunctionChapterTasteGate⟩,
      ⟨baireTwoFunctionFieldFaithful⟩,
      ⟨baireTwoFunctionNontrivial⟩,
      BaireTwoFunctionTasteGate_single_carrier_alignment_decode,
      BaireTwoFunctionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        BaireTwoFunctionTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.BaireTwoFunctionUp.TasteGate
