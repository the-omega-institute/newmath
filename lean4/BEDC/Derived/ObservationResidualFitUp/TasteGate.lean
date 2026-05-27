import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ObservationResidualFitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ObservationResidualFitUp : Type where
  | mk (O M R E L T C H P N : BHist) : ObservationResidualFitUp
  deriving DecidableEq

def observationResidualFitEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: observationResidualFitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: observationResidualFitEncodeBHist h

def observationResidualFitDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (observationResidualFitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (observationResidualFitDecodeBHist tail)

private theorem ObservationResidualFitTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      observationResidualFitDecodeBHist (observationResidualFitEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def observationResidualFitFields : ObservationResidualFitUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ObservationResidualFitUp.mk O M R E L T C H P N => [O, M, R, E, L, T, C, H, P, N]

def observationResidualFitToEventFlow : ObservationResidualFitUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ObservationResidualFitUp.mk O M R E L T C H P N =>
      [[BMark.b0],
        observationResidualFitEncodeBHist O,
        [BMark.b1, BMark.b0],
        observationResidualFitEncodeBHist M,
        [BMark.b1, BMark.b1, BMark.b0],
        observationResidualFitEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observationResidualFitEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observationResidualFitEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observationResidualFitEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observationResidualFitEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        observationResidualFitEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        observationResidualFitEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        observationResidualFitEncodeBHist N]

private def ObservationResidualFitTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      ObservationResidualFitTasteGate_single_carrier_alignment_eventAt index rest

def observationResidualFitFromEventFlow :
    EventFlow → Option ObservationResidualFitUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (ObservationResidualFitUp.mk
          (observationResidualFitDecodeBHist
            (ObservationResidualFitTasteGate_single_carrier_alignment_eventAt 1 ef))
          (observationResidualFitDecodeBHist
            (ObservationResidualFitTasteGate_single_carrier_alignment_eventAt 3 ef))
          (observationResidualFitDecodeBHist
            (ObservationResidualFitTasteGate_single_carrier_alignment_eventAt 5 ef))
          (observationResidualFitDecodeBHist
            (ObservationResidualFitTasteGate_single_carrier_alignment_eventAt 7 ef))
          (observationResidualFitDecodeBHist
            (ObservationResidualFitTasteGate_single_carrier_alignment_eventAt 9 ef))
          (observationResidualFitDecodeBHist
            (ObservationResidualFitTasteGate_single_carrier_alignment_eventAt 11 ef))
          (observationResidualFitDecodeBHist
            (ObservationResidualFitTasteGate_single_carrier_alignment_eventAt 13 ef))
          (observationResidualFitDecodeBHist
            (ObservationResidualFitTasteGate_single_carrier_alignment_eventAt 15 ef))
          (observationResidualFitDecodeBHist
            (ObservationResidualFitTasteGate_single_carrier_alignment_eventAt 17 ef))
          (observationResidualFitDecodeBHist
            (ObservationResidualFitTasteGate_single_carrier_alignment_eventAt 19 ef)))

private theorem ObservationResidualFitTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ObservationResidualFitUp,
      observationResidualFitFromEventFlow (observationResidualFitToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk O M R E L T C H P N =>
      change
        some
          (ObservationResidualFitUp.mk
            (observationResidualFitDecodeBHist (observationResidualFitEncodeBHist O))
            (observationResidualFitDecodeBHist (observationResidualFitEncodeBHist M))
            (observationResidualFitDecodeBHist (observationResidualFitEncodeBHist R))
            (observationResidualFitDecodeBHist (observationResidualFitEncodeBHist E))
            (observationResidualFitDecodeBHist (observationResidualFitEncodeBHist L))
            (observationResidualFitDecodeBHist (observationResidualFitEncodeBHist T))
            (observationResidualFitDecodeBHist (observationResidualFitEncodeBHist C))
            (observationResidualFitDecodeBHist (observationResidualFitEncodeBHist H))
            (observationResidualFitDecodeBHist (observationResidualFitEncodeBHist P))
            (observationResidualFitDecodeBHist (observationResidualFitEncodeBHist N))) =
          some (ObservationResidualFitUp.mk O M R E L T C H P N)
      rw [ObservationResidualFitTasteGate_single_carrier_alignment_decode O,
        ObservationResidualFitTasteGate_single_carrier_alignment_decode M,
        ObservationResidualFitTasteGate_single_carrier_alignment_decode R,
        ObservationResidualFitTasteGate_single_carrier_alignment_decode E,
        ObservationResidualFitTasteGate_single_carrier_alignment_decode L,
        ObservationResidualFitTasteGate_single_carrier_alignment_decode T,
        ObservationResidualFitTasteGate_single_carrier_alignment_decode C,
        ObservationResidualFitTasteGate_single_carrier_alignment_decode H,
        ObservationResidualFitTasteGate_single_carrier_alignment_decode P,
        ObservationResidualFitTasteGate_single_carrier_alignment_decode N]

private theorem ObservationResidualFitToEventFlow_injective
    {x y : ObservationResidualFitUp} :
    observationResidualFitToEventFlow x = observationResidualFitToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      observationResidualFitFromEventFlow (observationResidualFitToEventFlow x) =
        observationResidualFitFromEventFlow (observationResidualFitToEventFlow y) :=
    congrArg observationResidualFitFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ObservationResidualFitTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (ObservationResidualFitTasteGate_single_carrier_alignment_round_trip y)))

private theorem ObservationResidualFitTasteGate_single_carrier_alignment_fields :
    ∀ x y : ObservationResidualFitUp,
      observationResidualFitFields x = observationResidualFitFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk O₁ M₁ R₁ E₁ L₁ T₁ C₁ H₁ P₁ N₁ =>
      cases y with
      | mk O₂ M₂ R₂ E₂ L₂ T₂ C₂ H₂ P₂ N₂ =>
          cases hfields
          rfl

instance observationResidualFitBHistCarrier : BHistCarrier ObservationResidualFitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := observationResidualFitToEventFlow
  fromEventFlow := observationResidualFitFromEventFlow

instance observationResidualFitChapterTasteGate : ChapterTasteGate ObservationResidualFitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change observationResidualFitFromEventFlow (observationResidualFitToEventFlow x) = some x
    exact ObservationResidualFitTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ObservationResidualFitToEventFlow_injective heq)

instance observationResidualFitFieldFaithful : FieldFaithful ObservationResidualFitUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := observationResidualFitFields
  field_faithful := ObservationResidualFitTasteGate_single_carrier_alignment_fields

instance observationResidualFitNontrivial : Nontrivial ObservationResidualFitUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ObservationResidualFitUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ObservationResidualFitUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem ObservationResidualFitTasteGate_single_carrier_alignment :
    (∀ h : BHist, observationResidualFitDecodeBHist (observationResidualFitEncodeBHist h) = h) ∧
      observationResidualFitFields
          (ObservationResidualFitUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · exact ObservationResidualFitTasteGate_single_carrier_alignment_decode
  · rfl

end BEDC.Derived.ObservationResidualFitUp
