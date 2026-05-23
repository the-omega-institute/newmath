import BEDC.Derived.DyadicCoverRefinementUp
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicCoverRefinementUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def dyadicCoverRefinementEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicCoverRefinementEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicCoverRefinementEncodeBHist h

def dyadicCoverRefinementDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicCoverRefinementDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicCoverRefinementDecodeBHist tail)

private theorem DyadicCoverRefinementTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, dyadicCoverRefinementDecodeBHist (dyadicCoverRefinementEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def dyadicCoverRefinementFields : DyadicCoverRefinementUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicCoverRefinementUp.mk leftCover rightCover commonRefinement leftRestriction
      rightRestriction transport routes provenance name =>
      [leftCover, rightCover, commonRefinement, leftRestriction, rightRestriction, transport,
        routes, provenance, name]

def dyadicCoverRefinementToEventFlow : DyadicCoverRefinementUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (dyadicCoverRefinementFields x).map dyadicCoverRefinementEncodeBHist

private def DyadicCoverRefinementTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      DyadicCoverRefinementTasteGate_single_carrier_alignment_eventAt index rest

def dyadicCoverRefinementFromEventFlow (ef : EventFlow) : Option DyadicCoverRefinementUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DyadicCoverRefinementUp.mk
      (dyadicCoverRefinementDecodeBHist
        (DyadicCoverRefinementTasteGate_single_carrier_alignment_eventAt 0 ef))
      (dyadicCoverRefinementDecodeBHist
        (DyadicCoverRefinementTasteGate_single_carrier_alignment_eventAt 1 ef))
      (dyadicCoverRefinementDecodeBHist
        (DyadicCoverRefinementTasteGate_single_carrier_alignment_eventAt 2 ef))
      (dyadicCoverRefinementDecodeBHist
        (DyadicCoverRefinementTasteGate_single_carrier_alignment_eventAt 3 ef))
      (dyadicCoverRefinementDecodeBHist
        (DyadicCoverRefinementTasteGate_single_carrier_alignment_eventAt 4 ef))
      (dyadicCoverRefinementDecodeBHist
        (DyadicCoverRefinementTasteGate_single_carrier_alignment_eventAt 5 ef))
      (dyadicCoverRefinementDecodeBHist
        (DyadicCoverRefinementTasteGate_single_carrier_alignment_eventAt 6 ef))
      (dyadicCoverRefinementDecodeBHist
        (DyadicCoverRefinementTasteGate_single_carrier_alignment_eventAt 7 ef))
      (dyadicCoverRefinementDecodeBHist
        (DyadicCoverRefinementTasteGate_single_carrier_alignment_eventAt 8 ef)))

private theorem DyadicCoverRefinementTasteGate_single_carrier_alignment_round_trip
    (x : DyadicCoverRefinementUp) :
    dyadicCoverRefinementFromEventFlow (dyadicCoverRefinementToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk leftCover rightCover commonRefinement leftRestriction rightRestriction transport routes
      provenance name =>
      change
        some
          (DyadicCoverRefinementUp.mk
            (dyadicCoverRefinementDecodeBHist (dyadicCoverRefinementEncodeBHist leftCover))
            (dyadicCoverRefinementDecodeBHist (dyadicCoverRefinementEncodeBHist rightCover))
            (dyadicCoverRefinementDecodeBHist
              (dyadicCoverRefinementEncodeBHist commonRefinement))
            (dyadicCoverRefinementDecodeBHist
              (dyadicCoverRefinementEncodeBHist leftRestriction))
            (dyadicCoverRefinementDecodeBHist
              (dyadicCoverRefinementEncodeBHist rightRestriction))
            (dyadicCoverRefinementDecodeBHist (dyadicCoverRefinementEncodeBHist transport))
            (dyadicCoverRefinementDecodeBHist (dyadicCoverRefinementEncodeBHist routes))
            (dyadicCoverRefinementDecodeBHist (dyadicCoverRefinementEncodeBHist provenance))
            (dyadicCoverRefinementDecodeBHist (dyadicCoverRefinementEncodeBHist name))) =
          some
            (DyadicCoverRefinementUp.mk leftCover rightCover commonRefinement leftRestriction
              rightRestriction transport routes provenance name)
      rw [DyadicCoverRefinementTasteGate_single_carrier_alignment_decode_encode leftCover,
        DyadicCoverRefinementTasteGate_single_carrier_alignment_decode_encode rightCover,
        DyadicCoverRefinementTasteGate_single_carrier_alignment_decode_encode commonRefinement,
        DyadicCoverRefinementTasteGate_single_carrier_alignment_decode_encode leftRestriction,
        DyadicCoverRefinementTasteGate_single_carrier_alignment_decode_encode rightRestriction,
        DyadicCoverRefinementTasteGate_single_carrier_alignment_decode_encode transport,
        DyadicCoverRefinementTasteGate_single_carrier_alignment_decode_encode routes,
        DyadicCoverRefinementTasteGate_single_carrier_alignment_decode_encode provenance,
        DyadicCoverRefinementTasteGate_single_carrier_alignment_decode_encode name]

private theorem DyadicCoverRefinementTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DyadicCoverRefinementUp} :
    dyadicCoverRefinementToEventFlow x = dyadicCoverRefinementToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicCoverRefinementFromEventFlow (dyadicCoverRefinementToEventFlow x) =
        dyadicCoverRefinementFromEventFlow (dyadicCoverRefinementToEventFlow y) :=
    congrArg dyadicCoverRefinementFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DyadicCoverRefinementTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (DyadicCoverRefinementTasteGate_single_carrier_alignment_round_trip y)))

private theorem DyadicCoverRefinementTasteGate_single_carrier_alignment_fields :
    ∀ x y : DyadicCoverRefinementUp, dyadicCoverRefinementFields x =
      dyadicCoverRefinementFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk leftCover₁ rightCover₁ commonRefinement₁ leftRestriction₁ rightRestriction₁ transport₁
      routes₁ provenance₁ name₁ =>
      cases y with
      | mk leftCover₂ rightCover₂ commonRefinement₂ leftRestriction₂ rightRestriction₂ transport₂
          routes₂ provenance₂ name₂ =>
          cases hfields
          rfl

instance dyadicCoverRefinementBHistCarrier : BHistCarrier DyadicCoverRefinementUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicCoverRefinementToEventFlow
  fromEventFlow := dyadicCoverRefinementFromEventFlow

instance dyadicCoverRefinementChapterTasteGate :
    ChapterTasteGate DyadicCoverRefinementUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dyadicCoverRefinementFromEventFlow (dyadicCoverRefinementToEventFlow x) = some x
    exact DyadicCoverRefinementTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DyadicCoverRefinementTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance dyadicCoverRefinementFieldFaithful : FieldFaithful DyadicCoverRefinementUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := dyadicCoverRefinementFields
  field_faithful := DyadicCoverRefinementTasteGate_single_carrier_alignment_fields

instance dyadicCoverRefinementNontrivial :
    BEDC.Meta.TasteGate.Nontrivial DyadicCoverRefinementUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DyadicCoverRefinementUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DyadicCoverRefinementUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def dyadicCoverRefinementTasteGate : ChapterTasteGate DyadicCoverRefinementUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicCoverRefinementChapterTasteGate

theorem DyadicCoverRefinementTasteGate_single_carrier_alignment :
    (∀ h : BHist, dyadicCoverRefinementDecodeBHist (dyadicCoverRefinementEncodeBHist h) = h) ∧
      (∀ x : DyadicCoverRefinementUp,
        dyadicCoverRefinementFromEventFlow (dyadicCoverRefinementToEventFlow x) = some x) ∧
        (∀ x y : DyadicCoverRefinementUp,
          dyadicCoverRefinementToEventFlow x = dyadicCoverRefinementToEventFlow y → x = y) ∧
          dyadicCoverRefinementEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∀ x y : DyadicCoverRefinementUp,
              dyadicCoverRefinementFields x = dyadicCoverRefinementFields y → x = y) ∧
              (∃ x y : DyadicCoverRefinementUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨DyadicCoverRefinementTasteGate_single_carrier_alignment_decode_encode,
      DyadicCoverRefinementTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        DyadicCoverRefinementTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl,
      DyadicCoverRefinementTasteGate_single_carrier_alignment_fields,
      ⟨DyadicCoverRefinementUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
        DyadicCoverRefinementUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
        by
          intro h
          cases h⟩⟩

end BEDC.Derived.DyadicCoverRefinementUp
