import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyProductMertensUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyProductMertensUp : Type where
  | mk (A B W T R D S E H C Q N : BHist) : CauchyProductMertensUp
  deriving DecidableEq

def cauchyProductMertensEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyProductMertensEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyProductMertensEncodeBHist h

def cauchyProductMertensDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyProductMertensDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyProductMertensDecodeBHist tail)

private theorem CauchyProductMertensTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cauchyProductMertensDecodeBHist (cauchyProductMertensEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyProductMertensFields : CauchyProductMertensUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyProductMertensUp.mk A B W T R D S E H C Q N =>
      [A, B, W, T, R, D, S, E, H, C, Q, N]

def cauchyProductMertensToEventFlow : CauchyProductMertensUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyProductMertensFields x).map cauchyProductMertensEncodeBHist

private def cauchyProductMertensEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyProductMertensEventAt index rest

def cauchyProductMertensFromEventFlow (ef : EventFlow) :
    Option CauchyProductMertensUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyProductMertensUp.mk
      (cauchyProductMertensDecodeBHist (cauchyProductMertensEventAt 0 ef))
      (cauchyProductMertensDecodeBHist (cauchyProductMertensEventAt 1 ef))
      (cauchyProductMertensDecodeBHist (cauchyProductMertensEventAt 2 ef))
      (cauchyProductMertensDecodeBHist (cauchyProductMertensEventAt 3 ef))
      (cauchyProductMertensDecodeBHist (cauchyProductMertensEventAt 4 ef))
      (cauchyProductMertensDecodeBHist (cauchyProductMertensEventAt 5 ef))
      (cauchyProductMertensDecodeBHist (cauchyProductMertensEventAt 6 ef))
      (cauchyProductMertensDecodeBHist (cauchyProductMertensEventAt 7 ef))
      (cauchyProductMertensDecodeBHist (cauchyProductMertensEventAt 8 ef))
      (cauchyProductMertensDecodeBHist (cauchyProductMertensEventAt 9 ef))
      (cauchyProductMertensDecodeBHist (cauchyProductMertensEventAt 10 ef))
      (cauchyProductMertensDecodeBHist (cauchyProductMertensEventAt 11 ef)))

private theorem CauchyProductMertensTasteGate_single_carrier_alignment_round_trip
    (x : CauchyProductMertensUp) :
    cauchyProductMertensFromEventFlow (cauchyProductMertensToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk A B W T R D S E H C Q N =>
      change
        some
          (CauchyProductMertensUp.mk
            (cauchyProductMertensDecodeBHist (cauchyProductMertensEncodeBHist A))
            (cauchyProductMertensDecodeBHist (cauchyProductMertensEncodeBHist B))
            (cauchyProductMertensDecodeBHist (cauchyProductMertensEncodeBHist W))
            (cauchyProductMertensDecodeBHist (cauchyProductMertensEncodeBHist T))
            (cauchyProductMertensDecodeBHist (cauchyProductMertensEncodeBHist R))
            (cauchyProductMertensDecodeBHist (cauchyProductMertensEncodeBHist D))
            (cauchyProductMertensDecodeBHist (cauchyProductMertensEncodeBHist S))
            (cauchyProductMertensDecodeBHist (cauchyProductMertensEncodeBHist E))
            (cauchyProductMertensDecodeBHist (cauchyProductMertensEncodeBHist H))
            (cauchyProductMertensDecodeBHist (cauchyProductMertensEncodeBHist C))
            (cauchyProductMertensDecodeBHist (cauchyProductMertensEncodeBHist Q))
            (cauchyProductMertensDecodeBHist (cauchyProductMertensEncodeBHist N))) =
          some (CauchyProductMertensUp.mk A B W T R D S E H C Q N)
      rw [CauchyProductMertensTasteGate_single_carrier_alignment_decode_encode A,
        CauchyProductMertensTasteGate_single_carrier_alignment_decode_encode B,
        CauchyProductMertensTasteGate_single_carrier_alignment_decode_encode W,
        CauchyProductMertensTasteGate_single_carrier_alignment_decode_encode T,
        CauchyProductMertensTasteGate_single_carrier_alignment_decode_encode R,
        CauchyProductMertensTasteGate_single_carrier_alignment_decode_encode D,
        CauchyProductMertensTasteGate_single_carrier_alignment_decode_encode S,
        CauchyProductMertensTasteGate_single_carrier_alignment_decode_encode E,
        CauchyProductMertensTasteGate_single_carrier_alignment_decode_encode H,
        CauchyProductMertensTasteGate_single_carrier_alignment_decode_encode C,
        CauchyProductMertensTasteGate_single_carrier_alignment_decode_encode Q,
        CauchyProductMertensTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchyProductMertensTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyProductMertensUp} :
    cauchyProductMertensToEventFlow x = cauchyProductMertensToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyProductMertensFromEventFlow (cauchyProductMertensToEventFlow x) =
        cauchyProductMertensFromEventFlow (cauchyProductMertensToEventFlow y) :=
    congrArg cauchyProductMertensFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyProductMertensTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CauchyProductMertensTasteGate_single_carrier_alignment_round_trip y)))

private theorem CauchyProductMertensTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : CauchyProductMertensUp,
      cauchyProductMertensFields x = cauchyProductMertensFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk A₁ B₁ W₁ T₁ R₁ D₁ S₁ E₁ H₁ C₁ Q₁ N₁ =>
      cases y with
      | mk A₂ B₂ W₂ T₂ R₂ D₂ S₂ E₂ H₂ C₂ Q₂ N₂ =>
          cases hfields
          rfl

instance cauchyProductMertensBHistCarrier :
    BHistCarrier CauchyProductMertensUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyProductMertensToEventFlow
  fromEventFlow := cauchyProductMertensFromEventFlow

instance cauchyProductMertensChapterTasteGate :
    ChapterTasteGate CauchyProductMertensUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyProductMertensFromEventFlow
      (cauchyProductMertensToEventFlow x) = some x
    exact CauchyProductMertensTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyProductMertensTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance cauchyProductMertensFieldFaithful :
    FieldFaithful CauchyProductMertensUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyProductMertensFields
  field_faithful := CauchyProductMertensTasteGate_single_carrier_alignment_fields_faithful

instance cauchyProductMertensNontrivial : Nontrivial CauchyProductMertensUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyProductMertensUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      CauchyProductMertensUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def CauchyProductMertensTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate CauchyProductMertensUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyProductMertensChapterTasteGate

theorem CauchyProductMertensTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyProductMertensDecodeBHist (cauchyProductMertensEncodeBHist h) = h) ∧
      (∀ x : CauchyProductMertensUp,
        cauchyProductMertensFromEventFlow (cauchyProductMertensToEventFlow x) = some x) ∧
      (∀ x y : CauchyProductMertensUp,
        cauchyProductMertensToEventFlow x = cauchyProductMertensToEventFlow y →
          x = y) ∧
      cauchyProductMertensEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CauchyProductMertensTasteGate_single_carrier_alignment_decode_encode,
      CauchyProductMertensTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq =>
        CauchyProductMertensTasteGate_single_carrier_alignment_toEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.CauchyProductMertensUp
