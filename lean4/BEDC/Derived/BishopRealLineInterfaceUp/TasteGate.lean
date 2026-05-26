import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopRealLineInterfaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopRealLineInterfaceUp : Type where
  | mk (D W R E Q H C P N : BHist) : BishopRealLineInterfaceUp
  deriving DecidableEq

def bishopRealLineInterfaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopRealLineInterfaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopRealLineInterfaceEncodeBHist h

def bishopRealLineInterfaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopRealLineInterfaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopRealLineInterfaceDecodeBHist tail)

private theorem BishopRealLineInterfaceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      bishopRealLineInterfaceDecodeBHist (bishopRealLineInterfaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopRealLineInterfaceFields : BishopRealLineInterfaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopRealLineInterfaceUp.mk D W R E Q H C P N => [D, W, R, E, Q, H, C, P, N]

def bishopRealLineInterfaceToEventFlow : BishopRealLineInterfaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (bishopRealLineInterfaceFields x).map bishopRealLineInterfaceEncodeBHist

private def bishopRealLineInterfaceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopRealLineInterfaceEventAtDefault index rest

def bishopRealLineInterfaceFromEventFlow : EventFlow → Option BishopRealLineInterfaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (BishopRealLineInterfaceUp.mk
        (bishopRealLineInterfaceDecodeBHist (bishopRealLineInterfaceEventAtDefault 0 ef))
        (bishopRealLineInterfaceDecodeBHist (bishopRealLineInterfaceEventAtDefault 1 ef))
        (bishopRealLineInterfaceDecodeBHist (bishopRealLineInterfaceEventAtDefault 2 ef))
        (bishopRealLineInterfaceDecodeBHist (bishopRealLineInterfaceEventAtDefault 3 ef))
        (bishopRealLineInterfaceDecodeBHist (bishopRealLineInterfaceEventAtDefault 4 ef))
        (bishopRealLineInterfaceDecodeBHist (bishopRealLineInterfaceEventAtDefault 5 ef))
        (bishopRealLineInterfaceDecodeBHist (bishopRealLineInterfaceEventAtDefault 6 ef))
        (bishopRealLineInterfaceDecodeBHist (bishopRealLineInterfaceEventAtDefault 7 ef))
        (bishopRealLineInterfaceDecodeBHist (bishopRealLineInterfaceEventAtDefault 8 ef)))

private theorem BishopRealLineInterfaceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BishopRealLineInterfaceUp,
      bishopRealLineInterfaceFromEventFlow (bishopRealLineInterfaceToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D W R E Q H C P N =>
      change
        some
          (BishopRealLineInterfaceUp.mk
            (bishopRealLineInterfaceDecodeBHist (bishopRealLineInterfaceEncodeBHist D))
            (bishopRealLineInterfaceDecodeBHist (bishopRealLineInterfaceEncodeBHist W))
            (bishopRealLineInterfaceDecodeBHist (bishopRealLineInterfaceEncodeBHist R))
            (bishopRealLineInterfaceDecodeBHist (bishopRealLineInterfaceEncodeBHist E))
            (bishopRealLineInterfaceDecodeBHist (bishopRealLineInterfaceEncodeBHist Q))
            (bishopRealLineInterfaceDecodeBHist (bishopRealLineInterfaceEncodeBHist H))
            (bishopRealLineInterfaceDecodeBHist (bishopRealLineInterfaceEncodeBHist C))
            (bishopRealLineInterfaceDecodeBHist (bishopRealLineInterfaceEncodeBHist P))
            (bishopRealLineInterfaceDecodeBHist (bishopRealLineInterfaceEncodeBHist N))) =
          some (BishopRealLineInterfaceUp.mk D W R E Q H C P N)
      rw [BishopRealLineInterfaceTasteGate_single_carrier_alignment_decode_encode D,
        BishopRealLineInterfaceTasteGate_single_carrier_alignment_decode_encode W,
        BishopRealLineInterfaceTasteGate_single_carrier_alignment_decode_encode R,
        BishopRealLineInterfaceTasteGate_single_carrier_alignment_decode_encode E,
        BishopRealLineInterfaceTasteGate_single_carrier_alignment_decode_encode Q,
        BishopRealLineInterfaceTasteGate_single_carrier_alignment_decode_encode H,
        BishopRealLineInterfaceTasteGate_single_carrier_alignment_decode_encode C,
        BishopRealLineInterfaceTasteGate_single_carrier_alignment_decode_encode P,
        BishopRealLineInterfaceTasteGate_single_carrier_alignment_decode_encode N]

private theorem BishopRealLineInterfaceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BishopRealLineInterfaceUp} :
    bishopRealLineInterfaceToEventFlow x = bishopRealLineInterfaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopRealLineInterfaceFromEventFlow (bishopRealLineInterfaceToEventFlow x) =
        bishopRealLineInterfaceFromEventFlow (bishopRealLineInterfaceToEventFlow y) :=
    congrArg bishopRealLineInterfaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BishopRealLineInterfaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopRealLineInterfaceTasteGate_single_carrier_alignment_round_trip y)))

private theorem BishopRealLineInterfaceTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : BishopRealLineInterfaceUp,
      bishopRealLineInterfaceFields x = bishopRealLineInterfaceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk D₁ W₁ R₁ E₁ Q₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk D₂ W₂ R₂ E₂ Q₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hD tail0
          injection tail0 with hW tail1
          injection tail1 with hR tail2
          injection tail2 with hE tail3
          injection tail3 with hQ tail4
          injection tail4 with hH tail5
          injection tail5 with hC tail6
          injection tail6 with hP tail7
          injection tail7 with hN _
          subst hD
          subst hW
          subst hR
          subst hE
          subst hQ
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance bishopRealLineInterfaceBHistCarrier : BHistCarrier BishopRealLineInterfaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopRealLineInterfaceToEventFlow
  fromEventFlow := bishopRealLineInterfaceFromEventFlow

instance bishopRealLineInterfaceChapterTasteGate :
    ChapterTasteGate BishopRealLineInterfaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bishopRealLineInterfaceFromEventFlow (bishopRealLineInterfaceToEventFlow x) =
      some x
    exact BishopRealLineInterfaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (BishopRealLineInterfaceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance bishopRealLineInterfaceFieldFaithful : FieldFaithful BishopRealLineInterfaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bishopRealLineInterfaceFields
  field_faithful := BishopRealLineInterfaceTasteGate_single_carrier_alignment_fields_faithful

instance bishopRealLineInterfaceNontrivial : Nontrivial BishopRealLineInterfaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BishopRealLineInterfaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BishopRealLineInterfaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BishopRealLineInterfaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopRealLineInterfaceChapterTasteGate

theorem BishopRealLineInterfaceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      bishopRealLineInterfaceDecodeBHist (bishopRealLineInterfaceEncodeBHist h) = h) ∧
      (∀ x : BishopRealLineInterfaceUp,
        bishopRealLineInterfaceFromEventFlow (bishopRealLineInterfaceToEventFlow x) =
          some x) ∧
        (∀ x y : BishopRealLineInterfaceUp,
          bishopRealLineInterfaceToEventFlow x = bishopRealLineInterfaceToEventFlow y →
            x = y) ∧
          bishopRealLineInterfaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨BishopRealLineInterfaceTasteGate_single_carrier_alignment_decode_encode,
      BishopRealLineInterfaceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        BishopRealLineInterfaceTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.BishopRealLineInterfaceUp
