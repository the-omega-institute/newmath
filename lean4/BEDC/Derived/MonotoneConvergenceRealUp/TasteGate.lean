import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MonotoneConvergenceRealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MonotoneConvergenceRealUp : Type where
  | mk (X S M B C L R H T P N : BHist) : MonotoneConvergenceRealUp
  deriving DecidableEq

def monotoneConvergenceRealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: monotoneConvergenceRealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: monotoneConvergenceRealEncodeBHist h

def monotoneConvergenceRealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (monotoneConvergenceRealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (monotoneConvergenceRealDecodeBHist tail)

private theorem MonotoneConvergenceRealTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      monotoneConvergenceRealDecodeBHist (monotoneConvergenceRealEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def monotoneConvergenceRealFields : MonotoneConvergenceRealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MonotoneConvergenceRealUp.mk X S M B C L R H T P N => [X, S, M, B, C, L, R, H, T, P, N]

def monotoneConvergenceRealToEventFlow : MonotoneConvergenceRealUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (monotoneConvergenceRealFields x).map monotoneConvergenceRealEncodeBHist

private def monotoneConvergenceRealEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => monotoneConvergenceRealEventAtDefault index rest

def monotoneConvergenceRealFromEventFlow
    (ef : EventFlow) : Option MonotoneConvergenceRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MonotoneConvergenceRealUp.mk
      (monotoneConvergenceRealDecodeBHist (monotoneConvergenceRealEventAtDefault 0 ef))
      (monotoneConvergenceRealDecodeBHist (monotoneConvergenceRealEventAtDefault 1 ef))
      (monotoneConvergenceRealDecodeBHist (monotoneConvergenceRealEventAtDefault 2 ef))
      (monotoneConvergenceRealDecodeBHist (monotoneConvergenceRealEventAtDefault 3 ef))
      (monotoneConvergenceRealDecodeBHist (monotoneConvergenceRealEventAtDefault 4 ef))
      (monotoneConvergenceRealDecodeBHist (monotoneConvergenceRealEventAtDefault 5 ef))
      (monotoneConvergenceRealDecodeBHist (monotoneConvergenceRealEventAtDefault 6 ef))
      (monotoneConvergenceRealDecodeBHist (monotoneConvergenceRealEventAtDefault 7 ef))
      (monotoneConvergenceRealDecodeBHist (monotoneConvergenceRealEventAtDefault 8 ef))
      (monotoneConvergenceRealDecodeBHist (monotoneConvergenceRealEventAtDefault 9 ef))
      (monotoneConvergenceRealDecodeBHist (monotoneConvergenceRealEventAtDefault 10 ef)))

private theorem MonotoneConvergenceRealTasteGate_single_carrier_alignment_round_trip :
    ∀ x : MonotoneConvergenceRealUp,
      monotoneConvergenceRealFromEventFlow (monotoneConvergenceRealToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X S M B C L R H T P N =>
      change
        some
          (MonotoneConvergenceRealUp.mk
            (monotoneConvergenceRealDecodeBHist (monotoneConvergenceRealEncodeBHist X))
            (monotoneConvergenceRealDecodeBHist (monotoneConvergenceRealEncodeBHist S))
            (monotoneConvergenceRealDecodeBHist (monotoneConvergenceRealEncodeBHist M))
            (monotoneConvergenceRealDecodeBHist (monotoneConvergenceRealEncodeBHist B))
            (monotoneConvergenceRealDecodeBHist (monotoneConvergenceRealEncodeBHist C))
            (monotoneConvergenceRealDecodeBHist (monotoneConvergenceRealEncodeBHist L))
            (monotoneConvergenceRealDecodeBHist (monotoneConvergenceRealEncodeBHist R))
            (monotoneConvergenceRealDecodeBHist (monotoneConvergenceRealEncodeBHist H))
            (monotoneConvergenceRealDecodeBHist (monotoneConvergenceRealEncodeBHist T))
            (monotoneConvergenceRealDecodeBHist (monotoneConvergenceRealEncodeBHist P))
            (monotoneConvergenceRealDecodeBHist (monotoneConvergenceRealEncodeBHist N))) =
          some (MonotoneConvergenceRealUp.mk X S M B C L R H T P N)
      rw [MonotoneConvergenceRealTasteGate_single_carrier_alignment_decode X,
        MonotoneConvergenceRealTasteGate_single_carrier_alignment_decode S,
        MonotoneConvergenceRealTasteGate_single_carrier_alignment_decode M,
        MonotoneConvergenceRealTasteGate_single_carrier_alignment_decode B,
        MonotoneConvergenceRealTasteGate_single_carrier_alignment_decode C,
        MonotoneConvergenceRealTasteGate_single_carrier_alignment_decode L,
        MonotoneConvergenceRealTasteGate_single_carrier_alignment_decode R,
        MonotoneConvergenceRealTasteGate_single_carrier_alignment_decode H,
        MonotoneConvergenceRealTasteGate_single_carrier_alignment_decode T,
        MonotoneConvergenceRealTasteGate_single_carrier_alignment_decode P,
        MonotoneConvergenceRealTasteGate_single_carrier_alignment_decode N]

private theorem MonotoneConvergenceRealTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : MonotoneConvergenceRealUp} :
    monotoneConvergenceRealToEventFlow x = monotoneConvergenceRealToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      monotoneConvergenceRealFromEventFlow (monotoneConvergenceRealToEventFlow x) =
        monotoneConvergenceRealFromEventFlow (monotoneConvergenceRealToEventFlow y) :=
    congrArg monotoneConvergenceRealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (MonotoneConvergenceRealTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (MonotoneConvergenceRealTasteGate_single_carrier_alignment_round_trip y)))

private theorem MonotoneConvergenceRealTasteGate_single_carrier_alignment_fields :
    ∀ x y : MonotoneConvergenceRealUp,
      monotoneConvergenceRealFields x = monotoneConvergenceRealFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X₁ S₁ M₁ B₁ C₁ L₁ R₁ H₁ T₁ P₁ N₁ =>
      cases y with
      | mk X₂ S₂ M₂ B₂ C₂ L₂ R₂ H₂ T₂ P₂ N₂ =>
          cases hfields
          rfl

instance monotoneConvergenceRealBHistCarrier :
    BHistCarrier MonotoneConvergenceRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := monotoneConvergenceRealToEventFlow
  fromEventFlow := monotoneConvergenceRealFromEventFlow

instance monotoneConvergenceRealChapterTasteGate :
    ChapterTasteGate MonotoneConvergenceRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      monotoneConvergenceRealFromEventFlow (monotoneConvergenceRealToEventFlow x) =
        some x
    exact MonotoneConvergenceRealTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (MonotoneConvergenceRealTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance monotoneConvergenceRealFieldFaithful :
    FieldFaithful MonotoneConvergenceRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := monotoneConvergenceRealFields
  field_faithful := MonotoneConvergenceRealTasteGate_single_carrier_alignment_fields

instance monotoneConvergenceRealNontrivial :
    BEDC.Meta.TasteGate.Nontrivial MonotoneConvergenceRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MonotoneConvergenceRealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MonotoneConvergenceRealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MonotoneConvergenceRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  monotoneConvergenceRealChapterTasteGate

theorem MonotoneConvergenceRealTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      monotoneConvergenceRealDecodeBHist (monotoneConvergenceRealEncodeBHist h) =
        h) ∧
      (∀ x : MonotoneConvergenceRealUp,
        monotoneConvergenceRealFromEventFlow (monotoneConvergenceRealToEventFlow x) =
          some x) ∧
        (∀ x y : MonotoneConvergenceRealUp,
          monotoneConvergenceRealToEventFlow x = monotoneConvergenceRealToEventFlow y ->
            x = y) ∧
          monotoneConvergenceRealEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨MonotoneConvergenceRealTasteGate_single_carrier_alignment_decode,
      MonotoneConvergenceRealTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        MonotoneConvergenceRealTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.MonotoneConvergenceRealUp
