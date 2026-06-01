import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EpigraphUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EpigraphUp : Type where
  | mk (D V L O H C P N : BHist) : EpigraphUp
  deriving DecidableEq

def epigraphEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: epigraphEncodeBHist h
  | BHist.e1 h => BMark.b1 :: epigraphEncodeBHist h

def epigraphDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (epigraphDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (epigraphDecodeBHist tail)

private theorem EpigraphTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, epigraphDecodeBHist (epigraphEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def epigraphFields : EpigraphUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | EpigraphUp.mk D V L O H C P N => [D, V, L, O, H, C, P, N]

def epigraphToEventFlow : EpigraphUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (epigraphFields x).map epigraphEncodeBHist

private def epigraphEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => epigraphEventAt index rest

def epigraphFromEventFlow (ef : EventFlow) : Option EpigraphUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (EpigraphUp.mk
      (epigraphDecodeBHist (epigraphEventAt 0 ef))
      (epigraphDecodeBHist (epigraphEventAt 1 ef))
      (epigraphDecodeBHist (epigraphEventAt 2 ef))
      (epigraphDecodeBHist (epigraphEventAt 3 ef))
      (epigraphDecodeBHist (epigraphEventAt 4 ef))
      (epigraphDecodeBHist (epigraphEventAt 5 ef))
      (epigraphDecodeBHist (epigraphEventAt 6 ef))
      (epigraphDecodeBHist (epigraphEventAt 7 ef)))

private theorem EpigraphTasteGate_single_carrier_alignment_round_trip
    (x : EpigraphUp) :
    epigraphFromEventFlow (epigraphToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk D V L O H C P N =>
      change
        some
          (EpigraphUp.mk
            (epigraphDecodeBHist (epigraphEncodeBHist D))
            (epigraphDecodeBHist (epigraphEncodeBHist V))
            (epigraphDecodeBHist (epigraphEncodeBHist L))
            (epigraphDecodeBHist (epigraphEncodeBHist O))
            (epigraphDecodeBHist (epigraphEncodeBHist H))
            (epigraphDecodeBHist (epigraphEncodeBHist C))
            (epigraphDecodeBHist (epigraphEncodeBHist P))
            (epigraphDecodeBHist (epigraphEncodeBHist N))) =
          some (EpigraphUp.mk D V L O H C P N)
      rw [EpigraphTasteGate_single_carrier_alignment_decode D,
        EpigraphTasteGate_single_carrier_alignment_decode V,
        EpigraphTasteGate_single_carrier_alignment_decode L,
        EpigraphTasteGate_single_carrier_alignment_decode O,
        EpigraphTasteGate_single_carrier_alignment_decode H,
        EpigraphTasteGate_single_carrier_alignment_decode C,
        EpigraphTasteGate_single_carrier_alignment_decode P,
        EpigraphTasteGate_single_carrier_alignment_decode N]

private theorem EpigraphTasteGate_single_carrier_alignment_injective {x y : EpigraphUp} :
    epigraphToEventFlow x = epigraphToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      epigraphFromEventFlow (epigraphToEventFlow x) =
        epigraphFromEventFlow (epigraphToEventFlow y) :=
    congrArg epigraphFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (EpigraphTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (EpigraphTasteGate_single_carrier_alignment_round_trip y)))

private theorem EpigraphTasteGate_single_carrier_alignment_fields :
    ∀ x y : EpigraphUp, epigraphFields x = epigraphFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk D₁ V₁ L₁ O₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk D₂ V₂ L₂ O₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance epigraphBHistCarrier : BHistCarrier EpigraphUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := epigraphToEventFlow
  fromEventFlow := epigraphFromEventFlow

instance epigraphChapterTasteGate : ChapterTasteGate EpigraphUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change epigraphFromEventFlow (epigraphToEventFlow x) = some x
    exact EpigraphTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (EpigraphTasteGate_single_carrier_alignment_injective heq)

instance epigraphFieldFaithful : FieldFaithful EpigraphUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := epigraphFields
  field_faithful := EpigraphTasteGate_single_carrier_alignment_fields

instance epigraphNontrivial : Nontrivial EpigraphUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨EpigraphUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      EpigraphUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def epigraphTasteGate : ChapterTasteGate EpigraphUp :=
  -- BEDC touchpoint anchor: BHist BMark
  epigraphChapterTasteGate

theorem EpigraphTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate EpigraphUp) ∧
      Nonempty (FieldFaithful EpigraphUp) ∧
        Nonempty (Nontrivial EpigraphUp) ∧
          (∀ h : BHist, epigraphDecodeBHist (epigraphEncodeBHist h) = h) ∧
            (∀ x : EpigraphUp, epigraphFromEventFlow (epigraphToEventFlow x) = some x) ∧
              (∀ x y : EpigraphUp,
                epigraphToEventFlow x = epigraphToEventFlow y -> x = y) ∧
                epigraphEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨epigraphChapterTasteGate⟩,
      ⟨epigraphFieldFaithful⟩,
      ⟨epigraphNontrivial⟩,
      EpigraphTasteGate_single_carrier_alignment_decode,
      EpigraphTasteGate_single_carrier_alignment_round_trip,
      fun x y => EpigraphTasteGate_single_carrier_alignment_injective,
      rfl⟩

end BEDC.Derived.EpigraphUp.TasteGate
