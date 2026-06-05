import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealModulusExtractionUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealModulusExtractionUp : Type where
  | mk (D S R E T C P N : BHist) : RealModulusExtractionUp
  deriving DecidableEq

def realModulusExtractionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realModulusExtractionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realModulusExtractionEncodeBHist h

def realModulusExtractionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realModulusExtractionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realModulusExtractionDecodeBHist tail)

private theorem RealModulusExtractionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      realModulusExtractionDecodeBHist (realModulusExtractionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realModulusExtractionFields : RealModulusExtractionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealModulusExtractionUp.mk D S R E T C P N => [D, S, R, E, T, C, P, N]

def realModulusExtractionToEventFlow : RealModulusExtractionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (realModulusExtractionFields x).map realModulusExtractionEncodeBHist

private def realModulusExtractionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realModulusExtractionEventAtDefault index rest

def realModulusExtractionFromEventFlow
    (ef : EventFlow) : Option RealModulusExtractionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealModulusExtractionUp.mk
      (realModulusExtractionDecodeBHist (realModulusExtractionEventAtDefault 0 ef))
      (realModulusExtractionDecodeBHist (realModulusExtractionEventAtDefault 1 ef))
      (realModulusExtractionDecodeBHist (realModulusExtractionEventAtDefault 2 ef))
      (realModulusExtractionDecodeBHist (realModulusExtractionEventAtDefault 3 ef))
      (realModulusExtractionDecodeBHist (realModulusExtractionEventAtDefault 4 ef))
      (realModulusExtractionDecodeBHist (realModulusExtractionEventAtDefault 5 ef))
      (realModulusExtractionDecodeBHist (realModulusExtractionEventAtDefault 6 ef))
      (realModulusExtractionDecodeBHist (realModulusExtractionEventAtDefault 7 ef)))

private theorem RealModulusExtractionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RealModulusExtractionUp,
      realModulusExtractionFromEventFlow (realModulusExtractionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D S R E T C P N =>
      change
        some
          (RealModulusExtractionUp.mk
            (realModulusExtractionDecodeBHist (realModulusExtractionEncodeBHist D))
            (realModulusExtractionDecodeBHist (realModulusExtractionEncodeBHist S))
            (realModulusExtractionDecodeBHist (realModulusExtractionEncodeBHist R))
            (realModulusExtractionDecodeBHist (realModulusExtractionEncodeBHist E))
            (realModulusExtractionDecodeBHist (realModulusExtractionEncodeBHist T))
            (realModulusExtractionDecodeBHist (realModulusExtractionEncodeBHist C))
            (realModulusExtractionDecodeBHist (realModulusExtractionEncodeBHist P))
            (realModulusExtractionDecodeBHist (realModulusExtractionEncodeBHist N))) =
          some (RealModulusExtractionUp.mk D S R E T C P N)
      rw [RealModulusExtractionTasteGate_single_carrier_alignment_decode D,
        RealModulusExtractionTasteGate_single_carrier_alignment_decode S,
        RealModulusExtractionTasteGate_single_carrier_alignment_decode R,
        RealModulusExtractionTasteGate_single_carrier_alignment_decode E,
        RealModulusExtractionTasteGate_single_carrier_alignment_decode T,
        RealModulusExtractionTasteGate_single_carrier_alignment_decode C,
        RealModulusExtractionTasteGate_single_carrier_alignment_decode P,
        RealModulusExtractionTasteGate_single_carrier_alignment_decode N]

private theorem RealModulusExtractionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RealModulusExtractionUp} :
    realModulusExtractionToEventFlow x = realModulusExtractionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realModulusExtractionFromEventFlow (realModulusExtractionToEventFlow x) =
        realModulusExtractionFromEventFlow (realModulusExtractionToEventFlow y) :=
    congrArg realModulusExtractionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RealModulusExtractionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RealModulusExtractionTasteGate_single_carrier_alignment_round_trip y)))

private theorem RealModulusExtractionTasteGate_single_carrier_alignment_fields :
    ∀ x y : RealModulusExtractionUp,
      realModulusExtractionFields x = realModulusExtractionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk D₁ S₁ R₁ E₁ T₁ C₁ P₁ N₁ =>
      cases y with
      | mk D₂ S₂ R₂ E₂ T₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance realModulusExtractionBHistCarrier :
    BHistCarrier RealModulusExtractionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realModulusExtractionToEventFlow
  fromEventFlow := realModulusExtractionFromEventFlow

instance realModulusExtractionChapterTasteGate :
    ChapterTasteGate RealModulusExtractionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realModulusExtractionFromEventFlow (realModulusExtractionToEventFlow x) =
      some x
    exact RealModulusExtractionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RealModulusExtractionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance realModulusExtractionFieldFaithful :
    FieldFaithful RealModulusExtractionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realModulusExtractionFields
  field_faithful := RealModulusExtractionTasteGate_single_carrier_alignment_fields

def taste_gate : ChapterTasteGate RealModulusExtractionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realModulusExtractionChapterTasteGate

theorem RealModulusExtractionTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier RealModulusExtractionUp) ∧
      Nonempty (ChapterTasteGate RealModulusExtractionUp) ∧
        ∀ D S R E T C P N precisionRead scheduleRead regularRead sealRead : BHist,
          Cont D S scheduleRead ->
            Cont scheduleRead R regularRead ->
              Cont regularRead E sealRead ->
                hsame sealRead sealRead := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame BHistCarrier ChapterTasteGate
  exact
    ⟨⟨realModulusExtractionBHistCarrier⟩,
      ⟨realModulusExtractionChapterTasteGate⟩,
      fun _D _S _R _E _T _C _P _N _precisionRead _scheduleRead _regularRead sealRead
        _scheduleRoute _regularRoute _sealRoute => hsame_refl sealRead⟩

end BEDC.Derived.RealModulusExtractionUp
