import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ConstructiveBolzanoWeierstrassUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ConstructiveBolzanoWeierstrassUp : Type where
  | mk (S B I T R Q E H C P N : BHist) : ConstructiveBolzanoWeierstrassUp
  deriving DecidableEq

def constructiveBolzanoWeierstrassEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: constructiveBolzanoWeierstrassEncodeBHist h
  | BHist.e1 h => BMark.b1 :: constructiveBolzanoWeierstrassEncodeBHist h

def constructiveBolzanoWeierstrassDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (constructiveBolzanoWeierstrassDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (constructiveBolzanoWeierstrassDecodeBHist tail)

private theorem ConstructiveBolzanoWeierstrassTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      constructiveBolzanoWeierstrassDecodeBHist
        (constructiveBolzanoWeierstrassEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def constructiveBolzanoWeierstrassFields :
    ConstructiveBolzanoWeierstrassUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ConstructiveBolzanoWeierstrassUp.mk S B I T R Q E H C P N =>
      [S, B, I, T, R, Q, E, H, C, P, N]

def constructiveBolzanoWeierstrassToEventFlow :
    ConstructiveBolzanoWeierstrassUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (constructiveBolzanoWeierstrassFields x).map
      constructiveBolzanoWeierstrassEncodeBHist

private def constructiveBolzanoWeierstrassEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      constructiveBolzanoWeierstrassEventAtDefault index rest

def constructiveBolzanoWeierstrassFromEventFlow
    (ef : EventFlow) : Option ConstructiveBolzanoWeierstrassUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ConstructiveBolzanoWeierstrassUp.mk
      (constructiveBolzanoWeierstrassDecodeBHist
        (constructiveBolzanoWeierstrassEventAtDefault 0 ef))
      (constructiveBolzanoWeierstrassDecodeBHist
        (constructiveBolzanoWeierstrassEventAtDefault 1 ef))
      (constructiveBolzanoWeierstrassDecodeBHist
        (constructiveBolzanoWeierstrassEventAtDefault 2 ef))
      (constructiveBolzanoWeierstrassDecodeBHist
        (constructiveBolzanoWeierstrassEventAtDefault 3 ef))
      (constructiveBolzanoWeierstrassDecodeBHist
        (constructiveBolzanoWeierstrassEventAtDefault 4 ef))
      (constructiveBolzanoWeierstrassDecodeBHist
        (constructiveBolzanoWeierstrassEventAtDefault 5 ef))
      (constructiveBolzanoWeierstrassDecodeBHist
        (constructiveBolzanoWeierstrassEventAtDefault 6 ef))
      (constructiveBolzanoWeierstrassDecodeBHist
        (constructiveBolzanoWeierstrassEventAtDefault 7 ef))
      (constructiveBolzanoWeierstrassDecodeBHist
        (constructiveBolzanoWeierstrassEventAtDefault 8 ef))
      (constructiveBolzanoWeierstrassDecodeBHist
        (constructiveBolzanoWeierstrassEventAtDefault 9 ef))
      (constructiveBolzanoWeierstrassDecodeBHist
        (constructiveBolzanoWeierstrassEventAtDefault 10 ef)))

private theorem ConstructiveBolzanoWeierstrassTasteGate_single_carrier_alignment_round_trip
    (x : ConstructiveBolzanoWeierstrassUp) :
    constructiveBolzanoWeierstrassFromEventFlow
      (constructiveBolzanoWeierstrassToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S B I T R Q E H C P N =>
      change
        some
          (ConstructiveBolzanoWeierstrassUp.mk
            (constructiveBolzanoWeierstrassDecodeBHist
              (constructiveBolzanoWeierstrassEncodeBHist S))
            (constructiveBolzanoWeierstrassDecodeBHist
              (constructiveBolzanoWeierstrassEncodeBHist B))
            (constructiveBolzanoWeierstrassDecodeBHist
              (constructiveBolzanoWeierstrassEncodeBHist I))
            (constructiveBolzanoWeierstrassDecodeBHist
              (constructiveBolzanoWeierstrassEncodeBHist T))
            (constructiveBolzanoWeierstrassDecodeBHist
              (constructiveBolzanoWeierstrassEncodeBHist R))
            (constructiveBolzanoWeierstrassDecodeBHist
              (constructiveBolzanoWeierstrassEncodeBHist Q))
            (constructiveBolzanoWeierstrassDecodeBHist
              (constructiveBolzanoWeierstrassEncodeBHist E))
            (constructiveBolzanoWeierstrassDecodeBHist
              (constructiveBolzanoWeierstrassEncodeBHist H))
            (constructiveBolzanoWeierstrassDecodeBHist
              (constructiveBolzanoWeierstrassEncodeBHist C))
            (constructiveBolzanoWeierstrassDecodeBHist
              (constructiveBolzanoWeierstrassEncodeBHist P))
            (constructiveBolzanoWeierstrassDecodeBHist
              (constructiveBolzanoWeierstrassEncodeBHist N))) =
          some (ConstructiveBolzanoWeierstrassUp.mk S B I T R Q E H C P N)
      rw [ConstructiveBolzanoWeierstrassTasteGate_single_carrier_alignment_decode_encode S,
        ConstructiveBolzanoWeierstrassTasteGate_single_carrier_alignment_decode_encode B,
        ConstructiveBolzanoWeierstrassTasteGate_single_carrier_alignment_decode_encode I,
        ConstructiveBolzanoWeierstrassTasteGate_single_carrier_alignment_decode_encode T,
        ConstructiveBolzanoWeierstrassTasteGate_single_carrier_alignment_decode_encode R,
        ConstructiveBolzanoWeierstrassTasteGate_single_carrier_alignment_decode_encode Q,
        ConstructiveBolzanoWeierstrassTasteGate_single_carrier_alignment_decode_encode E,
        ConstructiveBolzanoWeierstrassTasteGate_single_carrier_alignment_decode_encode H,
        ConstructiveBolzanoWeierstrassTasteGate_single_carrier_alignment_decode_encode C,
        ConstructiveBolzanoWeierstrassTasteGate_single_carrier_alignment_decode_encode P,
        ConstructiveBolzanoWeierstrassTasteGate_single_carrier_alignment_decode_encode N]

private theorem ConstructiveBolzanoWeierstrassTasteGate_single_carrier_alignment_injective
    {x y : ConstructiveBolzanoWeierstrassUp} :
    constructiveBolzanoWeierstrassToEventFlow x =
      constructiveBolzanoWeierstrassToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      constructiveBolzanoWeierstrassFromEventFlow
          (constructiveBolzanoWeierstrassToEventFlow x) =
        constructiveBolzanoWeierstrassFromEventFlow
          (constructiveBolzanoWeierstrassToEventFlow y) :=
    congrArg constructiveBolzanoWeierstrassFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ConstructiveBolzanoWeierstrassTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ConstructiveBolzanoWeierstrassTasteGate_single_carrier_alignment_round_trip y)))

private theorem ConstructiveBolzanoWeierstrassTasteGate_single_carrier_alignment_fields :
    ∀ x y : ConstructiveBolzanoWeierstrassUp,
      constructiveBolzanoWeierstrassFields x =
        constructiveBolzanoWeierstrassFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S₁ B₁ I₁ T₁ R₁ Q₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk S₂ B₂ I₂ T₂ R₂ Q₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance constructiveBolzanoWeierstrassBHistCarrier :
    BHistCarrier ConstructiveBolzanoWeierstrassUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := constructiveBolzanoWeierstrassToEventFlow
  fromEventFlow := constructiveBolzanoWeierstrassFromEventFlow

instance constructiveBolzanoWeierstrassChapterTasteGate :
    ChapterTasteGate ConstructiveBolzanoWeierstrassUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      constructiveBolzanoWeierstrassFromEventFlow
        (constructiveBolzanoWeierstrassToEventFlow x) = some x
    exact ConstructiveBolzanoWeierstrassTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (ConstructiveBolzanoWeierstrassTasteGate_single_carrier_alignment_injective heq)

instance constructiveBolzanoWeierstrassFieldFaithful :
    FieldFaithful ConstructiveBolzanoWeierstrassUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := constructiveBolzanoWeierstrassFields
  field_faithful := ConstructiveBolzanoWeierstrassTasteGate_single_carrier_alignment_fields

instance constructiveBolzanoWeierstrassNontrivial :
    Nontrivial ConstructiveBolzanoWeierstrassUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ConstructiveBolzanoWeierstrassUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      ConstructiveBolzanoWeierstrassUp.mk (BHist.e1 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem ConstructiveBolzanoWeierstrassTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      constructiveBolzanoWeierstrassDecodeBHist
        (constructiveBolzanoWeierstrassEncodeBHist h) = h) ∧
      (∀ x : ConstructiveBolzanoWeierstrassUp,
        constructiveBolzanoWeierstrassFromEventFlow
          (constructiveBolzanoWeierstrassToEventFlow x) = some x) ∧
        (∀ x y : ConstructiveBolzanoWeierstrassUp,
          constructiveBolzanoWeierstrassToEventFlow x =
            constructiveBolzanoWeierstrassToEventFlow y → x = y) ∧
          constructiveBolzanoWeierstrassEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨ConstructiveBolzanoWeierstrassTasteGate_single_carrier_alignment_decode_encode,
      ConstructiveBolzanoWeierstrassTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        ConstructiveBolzanoWeierstrassTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

end BEDC.Derived.ConstructiveBolzanoWeierstrassUp
