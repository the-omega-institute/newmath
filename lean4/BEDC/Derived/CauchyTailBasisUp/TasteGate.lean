import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyTailBasisUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyTailBasisUp : Type where
  | mk (T W D R E H C P N : BHist) : CauchyTailBasisUp
  deriving DecidableEq

def cauchyTailBasisEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyTailBasisEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyTailBasisEncodeBHist h

def cauchyTailBasisDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyTailBasisDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyTailBasisDecodeBHist tail)

private theorem CauchyTailBasisTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, cauchyTailBasisDecodeBHist (cauchyTailBasisEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyTailBasisFields : CauchyTailBasisUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyTailBasisUp.mk T W D R E H C P N => [T, W, D, R, E, H, C, P, N]

def cauchyTailBasisToEventFlow : CauchyTailBasisUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyTailBasisFields x).map cauchyTailBasisEncodeBHist

private def cauchyTailBasisEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyTailBasisEventAt index rest

def cauchyTailBasisFromEventFlow (ef : EventFlow) :
    Option CauchyTailBasisUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyTailBasisUp.mk
      (cauchyTailBasisDecodeBHist (cauchyTailBasisEventAt 0 ef))
      (cauchyTailBasisDecodeBHist (cauchyTailBasisEventAt 1 ef))
      (cauchyTailBasisDecodeBHist (cauchyTailBasisEventAt 2 ef))
      (cauchyTailBasisDecodeBHist (cauchyTailBasisEventAt 3 ef))
      (cauchyTailBasisDecodeBHist (cauchyTailBasisEventAt 4 ef))
      (cauchyTailBasisDecodeBHist (cauchyTailBasisEventAt 5 ef))
      (cauchyTailBasisDecodeBHist (cauchyTailBasisEventAt 6 ef))
      (cauchyTailBasisDecodeBHist (cauchyTailBasisEventAt 7 ef))
      (cauchyTailBasisDecodeBHist (cauchyTailBasisEventAt 8 ef)))

private theorem CauchyTailBasisTasteGate_single_carrier_alignment_round_trip
    (x : CauchyTailBasisUp) :
    cauchyTailBasisFromEventFlow (cauchyTailBasisToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk T W D R E H C P N =>
      change
        some
          (CauchyTailBasisUp.mk
            (cauchyTailBasisDecodeBHist (cauchyTailBasisEncodeBHist T))
            (cauchyTailBasisDecodeBHist (cauchyTailBasisEncodeBHist W))
            (cauchyTailBasisDecodeBHist (cauchyTailBasisEncodeBHist D))
            (cauchyTailBasisDecodeBHist (cauchyTailBasisEncodeBHist R))
            (cauchyTailBasisDecodeBHist (cauchyTailBasisEncodeBHist E))
            (cauchyTailBasisDecodeBHist (cauchyTailBasisEncodeBHist H))
            (cauchyTailBasisDecodeBHist (cauchyTailBasisEncodeBHist C))
            (cauchyTailBasisDecodeBHist (cauchyTailBasisEncodeBHist P))
            (cauchyTailBasisDecodeBHist (cauchyTailBasisEncodeBHist N))) =
          some (CauchyTailBasisUp.mk T W D R E H C P N)
      rw [CauchyTailBasisTasteGate_single_carrier_alignment_decode_encode T,
        CauchyTailBasisTasteGate_single_carrier_alignment_decode_encode W,
        CauchyTailBasisTasteGate_single_carrier_alignment_decode_encode D,
        CauchyTailBasisTasteGate_single_carrier_alignment_decode_encode R,
        CauchyTailBasisTasteGate_single_carrier_alignment_decode_encode E,
        CauchyTailBasisTasteGate_single_carrier_alignment_decode_encode H,
        CauchyTailBasisTasteGate_single_carrier_alignment_decode_encode C,
        CauchyTailBasisTasteGate_single_carrier_alignment_decode_encode P,
        CauchyTailBasisTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchyTailBasisTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyTailBasisUp} :
    cauchyTailBasisToEventFlow x = cauchyTailBasisToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyTailBasisFromEventFlow (cauchyTailBasisToEventFlow x) =
        cauchyTailBasisFromEventFlow (cauchyTailBasisToEventFlow y) :=
    congrArg cauchyTailBasisFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyTailBasisTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CauchyTailBasisTasteGate_single_carrier_alignment_round_trip y)))

private theorem CauchyTailBasisTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : CauchyTailBasisUp,
      cauchyTailBasisFields x = cauchyTailBasisFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk T₁ W₁ D₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk T₂ W₂ D₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance cauchyTailBasisBHistCarrier : BHistCarrier CauchyTailBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyTailBasisToEventFlow
  fromEventFlow := cauchyTailBasisFromEventFlow

instance cauchyTailBasisChapterTasteGate : ChapterTasteGate CauchyTailBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyTailBasisFromEventFlow (cauchyTailBasisToEventFlow x) = some x
    exact CauchyTailBasisTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyTailBasisTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance cauchyTailBasisFieldFaithful : FieldFaithful CauchyTailBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyTailBasisFields
  field_faithful := CauchyTailBasisTasteGate_single_carrier_alignment_field_faithful

instance cauchyTailBasisNontrivial :
    BEDC.Meta.TasteGate.Nontrivial CauchyTailBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyTailBasisUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyTailBasisUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def CauchyTailBasisTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate CauchyTailBasisUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyTailBasisChapterTasteGate

theorem CauchyTailBasisTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyTailBasisDecodeBHist (cauchyTailBasisEncodeBHist h) = h) ∧
      (∀ x : CauchyTailBasisUp,
        cauchyTailBasisFromEventFlow (cauchyTailBasisToEventFlow x) = some x) ∧
      (∀ x y : CauchyTailBasisUp,
        cauchyTailBasisToEventFlow x = cauchyTailBasisToEventFlow y → x = y) ∧
      cauchyTailBasisEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CauchyTailBasisTasteGate_single_carrier_alignment_decode_encode,
      CauchyTailBasisTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CauchyTailBasisTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CauchyTailBasisUp
