import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedRegSeqRatUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedRegSeqRatUp : Type where
  | mk (D S R Q W H K P N : BHist) : LocatedRegSeqRatUp
  deriving DecidableEq

def locatedRegSeqRatEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedRegSeqRatEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedRegSeqRatEncodeBHist h

def locatedRegSeqRatDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedRegSeqRatDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedRegSeqRatDecodeBHist tail)

private theorem locatedRegSeqRatDecode_encode :
    ∀ h : BHist, locatedRegSeqRatDecodeBHist (locatedRegSeqRatEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedRegSeqRatFields : LocatedRegSeqRatUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedRegSeqRatUp.mk D S R Q W H K P N => [D, S, R, Q, W, H, K, P, N]

def locatedRegSeqRatToEventFlow : LocatedRegSeqRatUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedRegSeqRatUp.mk D S R Q W H K P N =>
      [locatedRegSeqRatEncodeBHist D, locatedRegSeqRatEncodeBHist S,
        locatedRegSeqRatEncodeBHist R, locatedRegSeqRatEncodeBHist Q,
        locatedRegSeqRatEncodeBHist W, locatedRegSeqRatEncodeBHist H,
        locatedRegSeqRatEncodeBHist K, locatedRegSeqRatEncodeBHist P,
        locatedRegSeqRatEncodeBHist N]

private def locatedRegSeqRatEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatedRegSeqRatEventAt index rest

def locatedRegSeqRatFromEventFlow : EventFlow → Option LocatedRegSeqRatUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (LocatedRegSeqRatUp.mk
        (locatedRegSeqRatDecodeBHist (locatedRegSeqRatEventAt 0 ef))
        (locatedRegSeqRatDecodeBHist (locatedRegSeqRatEventAt 1 ef))
        (locatedRegSeqRatDecodeBHist (locatedRegSeqRatEventAt 2 ef))
        (locatedRegSeqRatDecodeBHist (locatedRegSeqRatEventAt 3 ef))
        (locatedRegSeqRatDecodeBHist (locatedRegSeqRatEventAt 4 ef))
        (locatedRegSeqRatDecodeBHist (locatedRegSeqRatEventAt 5 ef))
        (locatedRegSeqRatDecodeBHist (locatedRegSeqRatEventAt 6 ef))
        (locatedRegSeqRatDecodeBHist (locatedRegSeqRatEventAt 7 ef))
        (locatedRegSeqRatDecodeBHist (locatedRegSeqRatEventAt 8 ef)))

private theorem locatedRegSeqRat_round_trip :
    ∀ x : LocatedRegSeqRatUp,
      locatedRegSeqRatFromEventFlow (locatedRegSeqRatToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D S R Q W H K P N =>
      change
        some
            (LocatedRegSeqRatUp.mk
              (locatedRegSeqRatDecodeBHist (locatedRegSeqRatEncodeBHist D))
              (locatedRegSeqRatDecodeBHist (locatedRegSeqRatEncodeBHist S))
              (locatedRegSeqRatDecodeBHist (locatedRegSeqRatEncodeBHist R))
              (locatedRegSeqRatDecodeBHist (locatedRegSeqRatEncodeBHist Q))
              (locatedRegSeqRatDecodeBHist (locatedRegSeqRatEncodeBHist W))
              (locatedRegSeqRatDecodeBHist (locatedRegSeqRatEncodeBHist H))
              (locatedRegSeqRatDecodeBHist (locatedRegSeqRatEncodeBHist K))
              (locatedRegSeqRatDecodeBHist (locatedRegSeqRatEncodeBHist P))
              (locatedRegSeqRatDecodeBHist (locatedRegSeqRatEncodeBHist N))) =
          some (LocatedRegSeqRatUp.mk D S R Q W H K P N)
      rw [locatedRegSeqRatDecode_encode D, locatedRegSeqRatDecode_encode S,
        locatedRegSeqRatDecode_encode R, locatedRegSeqRatDecode_encode Q,
        locatedRegSeqRatDecode_encode W, locatedRegSeqRatDecode_encode H,
        locatedRegSeqRatDecode_encode K, locatedRegSeqRatDecode_encode P,
        locatedRegSeqRatDecode_encode N]

private theorem locatedRegSeqRatToEventFlow_injective {x y : LocatedRegSeqRatUp} :
    locatedRegSeqRatToEventFlow x = locatedRegSeqRatToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedRegSeqRatFromEventFlow (locatedRegSeqRatToEventFlow x) =
        locatedRegSeqRatFromEventFlow (locatedRegSeqRatToEventFlow y) :=
    congrArg locatedRegSeqRatFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (locatedRegSeqRat_round_trip x).symm
      (Eq.trans hread (locatedRegSeqRat_round_trip y)))

private theorem locatedRegSeqRatFieldFaithfulProof :
    ∀ x y : LocatedRegSeqRatUp, locatedRegSeqRatFields x = locatedRegSeqRatFields y → x = y :=
    by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk D₁ S₁ R₁ Q₁ W₁ H₁ K₁ P₁ N₁ =>
      cases y with
      | mk D₂ S₂ R₂ Q₂ W₂ H₂ K₂ P₂ N₂ =>
          cases hfields
          rfl

instance locatedRegSeqRatBHistCarrier : BHistCarrier LocatedRegSeqRatUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedRegSeqRatToEventFlow
  fromEventFlow := locatedRegSeqRatFromEventFlow

instance locatedRegSeqRatChapterTasteGate : ChapterTasteGate LocatedRegSeqRatUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedRegSeqRatFromEventFlow (locatedRegSeqRatToEventFlow x) = some x
    exact locatedRegSeqRat_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locatedRegSeqRatToEventFlow_injective heq)

instance locatedRegSeqRatFieldFaithful : FieldFaithful LocatedRegSeqRatUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := locatedRegSeqRatFields
  field_faithful := locatedRegSeqRatFieldFaithfulProof

instance locatedRegSeqRatNontrivial :
    BEDC.Meta.TasteGate.Nontrivial LocatedRegSeqRatUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LocatedRegSeqRatUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LocatedRegSeqRatUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem LocatedRegSeqRatTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate LocatedRegSeqRatUp) ∧
      Nonempty (FieldFaithful LocatedRegSeqRatUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial LocatedRegSeqRatUp) ∧
      (∀ h : BHist, locatedRegSeqRatDecodeBHist (locatedRegSeqRatEncodeBHist h) = h) ∧
      (∀ x : LocatedRegSeqRatUp,
        locatedRegSeqRatFromEventFlow (locatedRegSeqRatToEventFlow x) = some x) ∧
      (∀ x y : LocatedRegSeqRatUp,
        locatedRegSeqRatToEventFlow x = locatedRegSeqRatToEventFlow y → x = y) ∧
      locatedRegSeqRatEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨locatedRegSeqRatChapterTasteGate⟩
  constructor
  · exact ⟨locatedRegSeqRatFieldFaithful⟩
  constructor
  · exact ⟨locatedRegSeqRatNontrivial⟩
  constructor
  · exact locatedRegSeqRatDecode_encode
  constructor
  · exact locatedRegSeqRat_round_trip
  constructor
  · intro x y
    exact locatedRegSeqRatToEventFlow_injective
  · rfl

end BEDC.Derived.LocatedRegSeqRatUp
