import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SupportFunctionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SupportFunctionUp : Type where
  | mk (K V D E B H C P N : BHist) : SupportFunctionUp
  deriving DecidableEq

def supportFunctionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: supportFunctionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: supportFunctionEncodeBHist h

def supportFunctionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (supportFunctionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (supportFunctionDecodeBHist tail)

private theorem SupportFunctionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, supportFunctionDecodeBHist (supportFunctionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def supportFunctionFields : SupportFunctionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SupportFunctionUp.mk K V D E B H C P N => [K, V, D, E, B, H, C, P, N]

def supportFunctionToEventFlow : SupportFunctionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (supportFunctionFields x).map supportFunctionEncodeBHist

private def supportFunctionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => supportFunctionEventAt index rest

def supportFunctionFromEventFlow (ef : EventFlow) : Option SupportFunctionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SupportFunctionUp.mk
      (supportFunctionDecodeBHist (supportFunctionEventAt 0 ef))
      (supportFunctionDecodeBHist (supportFunctionEventAt 1 ef))
      (supportFunctionDecodeBHist (supportFunctionEventAt 2 ef))
      (supportFunctionDecodeBHist (supportFunctionEventAt 3 ef))
      (supportFunctionDecodeBHist (supportFunctionEventAt 4 ef))
      (supportFunctionDecodeBHist (supportFunctionEventAt 5 ef))
      (supportFunctionDecodeBHist (supportFunctionEventAt 6 ef))
      (supportFunctionDecodeBHist (supportFunctionEventAt 7 ef))
      (supportFunctionDecodeBHist (supportFunctionEventAt 8 ef)))

private theorem SupportFunctionTasteGate_single_carrier_alignment_round_trip
    (x : SupportFunctionUp) :
    supportFunctionFromEventFlow (supportFunctionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk K V D E B H C P N =>
      change
        some
          (SupportFunctionUp.mk
            (supportFunctionDecodeBHist (supportFunctionEncodeBHist K))
            (supportFunctionDecodeBHist (supportFunctionEncodeBHist V))
            (supportFunctionDecodeBHist (supportFunctionEncodeBHist D))
            (supportFunctionDecodeBHist (supportFunctionEncodeBHist E))
            (supportFunctionDecodeBHist (supportFunctionEncodeBHist B))
            (supportFunctionDecodeBHist (supportFunctionEncodeBHist H))
            (supportFunctionDecodeBHist (supportFunctionEncodeBHist C))
            (supportFunctionDecodeBHist (supportFunctionEncodeBHist P))
            (supportFunctionDecodeBHist (supportFunctionEncodeBHist N))) =
          some (SupportFunctionUp.mk K V D E B H C P N)
      rw [SupportFunctionTasteGate_single_carrier_alignment_decode K,
        SupportFunctionTasteGate_single_carrier_alignment_decode V,
        SupportFunctionTasteGate_single_carrier_alignment_decode D,
        SupportFunctionTasteGate_single_carrier_alignment_decode E,
        SupportFunctionTasteGate_single_carrier_alignment_decode B,
        SupportFunctionTasteGate_single_carrier_alignment_decode H,
        SupportFunctionTasteGate_single_carrier_alignment_decode C,
        SupportFunctionTasteGate_single_carrier_alignment_decode P,
        SupportFunctionTasteGate_single_carrier_alignment_decode N]

private theorem SupportFunctionTasteGate_single_carrier_alignment_injective
    {x y : SupportFunctionUp} :
    supportFunctionToEventFlow x = supportFunctionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      supportFunctionFromEventFlow (supportFunctionToEventFlow x) =
        supportFunctionFromEventFlow (supportFunctionToEventFlow y) :=
    congrArg supportFunctionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (SupportFunctionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (SupportFunctionTasteGate_single_carrier_alignment_round_trip y)))

private theorem SupportFunctionTasteGate_single_carrier_alignment_fields :
    ∀ x y : SupportFunctionUp, supportFunctionFields x = supportFunctionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K₁ V₁ D₁ E₁ B₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk K₂ V₂ D₂ E₂ B₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance supportFunctionBHistCarrier : BHistCarrier SupportFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := supportFunctionToEventFlow
  fromEventFlow := supportFunctionFromEventFlow

instance supportFunctionChapterTasteGate : ChapterTasteGate SupportFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change supportFunctionFromEventFlow (supportFunctionToEventFlow x) = some x
    exact SupportFunctionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SupportFunctionTasteGate_single_carrier_alignment_injective heq)

instance supportFunctionFieldFaithful : FieldFaithful SupportFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := supportFunctionFields
  field_faithful := SupportFunctionTasteGate_single_carrier_alignment_fields

instance supportFunctionNontrivial : Nontrivial SupportFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SupportFunctionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      SupportFunctionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem SupportFunctionTasteGate_single_carrier_alignment :
    (∀ h : BHist, supportFunctionDecodeBHist (supportFunctionEncodeBHist h) = h) ∧
      (∀ x : SupportFunctionUp,
        supportFunctionFromEventFlow (supportFunctionToEventFlow x) = some x) ∧
        (∀ x y : SupportFunctionUp,
          supportFunctionToEventFlow x = supportFunctionToEventFlow y → x = y) ∧
          supportFunctionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · exact SupportFunctionTasteGate_single_carrier_alignment_decode
  constructor
  · exact SupportFunctionTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact SupportFunctionTasteGate_single_carrier_alignment_injective heq
  · rfl

end BEDC.Derived.SupportFunctionUp
