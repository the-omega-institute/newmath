import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LawlikeCauchyRealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LawlikeCauchyRealUp : Type where
  | mk (G S D Q M E H C P N : BHist) : LawlikeCauchyRealUp
  deriving DecidableEq

def lawlikeCauchyRealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: lawlikeCauchyRealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: lawlikeCauchyRealEncodeBHist h

def lawlikeCauchyRealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (lawlikeCauchyRealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (lawlikeCauchyRealDecodeBHist tail)

private theorem LawlikeCauchyRealTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, lawlikeCauchyRealDecodeBHist (lawlikeCauchyRealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def lawlikeCauchyRealFields : LawlikeCauchyRealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LawlikeCauchyRealUp.mk G S D Q M E H C P N => [G, S, D, Q, M, E, H, C, P, N]

def lawlikeCauchyRealToEventFlow : LawlikeCauchyRealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (lawlikeCauchyRealFields x).map lawlikeCauchyRealEncodeBHist

private def lawlikeCauchyRealEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => lawlikeCauchyRealEventAt index rest

def lawlikeCauchyRealFromEventFlow (ef : EventFlow) : Option LawlikeCauchyRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LawlikeCauchyRealUp.mk
      (lawlikeCauchyRealDecodeBHist (lawlikeCauchyRealEventAt 0 ef))
      (lawlikeCauchyRealDecodeBHist (lawlikeCauchyRealEventAt 1 ef))
      (lawlikeCauchyRealDecodeBHist (lawlikeCauchyRealEventAt 2 ef))
      (lawlikeCauchyRealDecodeBHist (lawlikeCauchyRealEventAt 3 ef))
      (lawlikeCauchyRealDecodeBHist (lawlikeCauchyRealEventAt 4 ef))
      (lawlikeCauchyRealDecodeBHist (lawlikeCauchyRealEventAt 5 ef))
      (lawlikeCauchyRealDecodeBHist (lawlikeCauchyRealEventAt 6 ef))
      (lawlikeCauchyRealDecodeBHist (lawlikeCauchyRealEventAt 7 ef))
      (lawlikeCauchyRealDecodeBHist (lawlikeCauchyRealEventAt 8 ef))
      (lawlikeCauchyRealDecodeBHist (lawlikeCauchyRealEventAt 9 ef)))

private theorem LawlikeCauchyRealTasteGate_single_carrier_alignment_round_trip
    (x : LawlikeCauchyRealUp) :
    lawlikeCauchyRealFromEventFlow (lawlikeCauchyRealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk G S D Q M E H C P N =>
      change
        some
          (LawlikeCauchyRealUp.mk
            (lawlikeCauchyRealDecodeBHist (lawlikeCauchyRealEncodeBHist G))
            (lawlikeCauchyRealDecodeBHist (lawlikeCauchyRealEncodeBHist S))
            (lawlikeCauchyRealDecodeBHist (lawlikeCauchyRealEncodeBHist D))
            (lawlikeCauchyRealDecodeBHist (lawlikeCauchyRealEncodeBHist Q))
            (lawlikeCauchyRealDecodeBHist (lawlikeCauchyRealEncodeBHist M))
            (lawlikeCauchyRealDecodeBHist (lawlikeCauchyRealEncodeBHist E))
            (lawlikeCauchyRealDecodeBHist (lawlikeCauchyRealEncodeBHist H))
            (lawlikeCauchyRealDecodeBHist (lawlikeCauchyRealEncodeBHist C))
            (lawlikeCauchyRealDecodeBHist (lawlikeCauchyRealEncodeBHist P))
            (lawlikeCauchyRealDecodeBHist (lawlikeCauchyRealEncodeBHist N))) =
          some (LawlikeCauchyRealUp.mk G S D Q M E H C P N)
      rw [LawlikeCauchyRealTasteGate_single_carrier_alignment_decode_encode G,
        LawlikeCauchyRealTasteGate_single_carrier_alignment_decode_encode S,
        LawlikeCauchyRealTasteGate_single_carrier_alignment_decode_encode D,
        LawlikeCauchyRealTasteGate_single_carrier_alignment_decode_encode Q,
        LawlikeCauchyRealTasteGate_single_carrier_alignment_decode_encode M,
        LawlikeCauchyRealTasteGate_single_carrier_alignment_decode_encode E,
        LawlikeCauchyRealTasteGate_single_carrier_alignment_decode_encode H,
        LawlikeCauchyRealTasteGate_single_carrier_alignment_decode_encode C,
        LawlikeCauchyRealTasteGate_single_carrier_alignment_decode_encode P,
        LawlikeCauchyRealTasteGate_single_carrier_alignment_decode_encode N]

private theorem lawlikeCauchyRealToEventFlow_injective {x y : LawlikeCauchyRealUp} :
    lawlikeCauchyRealToEventFlow x = lawlikeCauchyRealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      lawlikeCauchyRealFromEventFlow (lawlikeCauchyRealToEventFlow x) =
        lawlikeCauchyRealFromEventFlow (lawlikeCauchyRealToEventFlow y) :=
    congrArg lawlikeCauchyRealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (LawlikeCauchyRealTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (LawlikeCauchyRealTasteGate_single_carrier_alignment_round_trip y)))

private theorem LawlikeCauchyRealTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : LawlikeCauchyRealUp,
      lawlikeCauchyRealFields x = lawlikeCauchyRealFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk G₁ S₁ D₁ Q₁ M₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk G₂ S₂ D₂ Q₂ M₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance lawlikeCauchyRealBHistCarrier : BHistCarrier LawlikeCauchyRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := lawlikeCauchyRealToEventFlow
  fromEventFlow := lawlikeCauchyRealFromEventFlow

instance lawlikeCauchyRealChapterTasteGate : ChapterTasteGate LawlikeCauchyRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change lawlikeCauchyRealFromEventFlow (lawlikeCauchyRealToEventFlow x) = some x
    exact LawlikeCauchyRealTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (lawlikeCauchyRealToEventFlow_injective heq)

instance lawlikeCauchyRealFieldFaithful : FieldFaithful LawlikeCauchyRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := lawlikeCauchyRealFields
  field_faithful := LawlikeCauchyRealTasteGate_single_carrier_alignment_fields_faithful

instance lawlikeCauchyRealNontrivial : Nontrivial LawlikeCauchyRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LawlikeCauchyRealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LawlikeCauchyRealUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def LawlikeCauchyRealTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate LawlikeCauchyRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  lawlikeCauchyRealChapterTasteGate

theorem LawlikeCauchyRealTasteGate_single_carrier_alignment :
    (∀ h : BHist, lawlikeCauchyRealDecodeBHist (lawlikeCauchyRealEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier LawlikeCauchyRealUp) ∧
        Nonempty (ChapterTasteGate LawlikeCauchyRealUp) ∧
          lawlikeCauchyRealEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨LawlikeCauchyRealTasteGate_single_carrier_alignment_decode_encode,
      ⟨lawlikeCauchyRealBHistCarrier⟩, ⟨lawlikeCauchyRealChapterTasteGate⟩, rfl⟩

end BEDC.Derived.LawlikeCauchyRealUp
