import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.VariationMeasureUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive VariationMeasureUp : Type where
  | mk (B J Pi E X D V A R H C P N : BHist) : VariationMeasureUp
  deriving DecidableEq

def variationMeasureEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: variationMeasureEncodeBHist h
  | BHist.e1 h => BMark.b1 :: variationMeasureEncodeBHist h

def variationMeasureDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (variationMeasureDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (variationMeasureDecodeBHist tail)

private theorem VariationMeasureTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, variationMeasureDecodeBHist (variationMeasureEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def variationMeasureFields : VariationMeasureUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | VariationMeasureUp.mk B J Pi E X D V A R H C P N =>
      [B, J, Pi, E, X, D, V, A, R, H, C, P, N]

def variationMeasureToEventFlow : VariationMeasureUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (variationMeasureFields x).map variationMeasureEncodeBHist

private def variationMeasureEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => variationMeasureEventAt index rest

def variationMeasureFromEventFlow (ef : EventFlow) : Option VariationMeasureUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (VariationMeasureUp.mk
      (variationMeasureDecodeBHist (variationMeasureEventAt 0 ef))
      (variationMeasureDecodeBHist (variationMeasureEventAt 1 ef))
      (variationMeasureDecodeBHist (variationMeasureEventAt 2 ef))
      (variationMeasureDecodeBHist (variationMeasureEventAt 3 ef))
      (variationMeasureDecodeBHist (variationMeasureEventAt 4 ef))
      (variationMeasureDecodeBHist (variationMeasureEventAt 5 ef))
      (variationMeasureDecodeBHist (variationMeasureEventAt 6 ef))
      (variationMeasureDecodeBHist (variationMeasureEventAt 7 ef))
      (variationMeasureDecodeBHist (variationMeasureEventAt 8 ef))
      (variationMeasureDecodeBHist (variationMeasureEventAt 9 ef))
      (variationMeasureDecodeBHist (variationMeasureEventAt 10 ef))
      (variationMeasureDecodeBHist (variationMeasureEventAt 11 ef))
      (variationMeasureDecodeBHist (variationMeasureEventAt 12 ef)))

private theorem VariationMeasureTasteGate_single_carrier_alignment_round_trip
    (x : VariationMeasureUp) :
    variationMeasureFromEventFlow (variationMeasureToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk B J Pi E X D V A R H C P N =>
      change
        some
          (VariationMeasureUp.mk
            (variationMeasureDecodeBHist (variationMeasureEncodeBHist B))
            (variationMeasureDecodeBHist (variationMeasureEncodeBHist J))
            (variationMeasureDecodeBHist (variationMeasureEncodeBHist Pi))
            (variationMeasureDecodeBHist (variationMeasureEncodeBHist E))
            (variationMeasureDecodeBHist (variationMeasureEncodeBHist X))
            (variationMeasureDecodeBHist (variationMeasureEncodeBHist D))
            (variationMeasureDecodeBHist (variationMeasureEncodeBHist V))
            (variationMeasureDecodeBHist (variationMeasureEncodeBHist A))
            (variationMeasureDecodeBHist (variationMeasureEncodeBHist R))
            (variationMeasureDecodeBHist (variationMeasureEncodeBHist H))
            (variationMeasureDecodeBHist (variationMeasureEncodeBHist C))
            (variationMeasureDecodeBHist (variationMeasureEncodeBHist P))
            (variationMeasureDecodeBHist (variationMeasureEncodeBHist N))) =
          some (VariationMeasureUp.mk B J Pi E X D V A R H C P N)
      rw [VariationMeasureTasteGate_single_carrier_alignment_decode_encode B,
        VariationMeasureTasteGate_single_carrier_alignment_decode_encode J,
        VariationMeasureTasteGate_single_carrier_alignment_decode_encode Pi,
        VariationMeasureTasteGate_single_carrier_alignment_decode_encode E,
        VariationMeasureTasteGate_single_carrier_alignment_decode_encode X,
        VariationMeasureTasteGate_single_carrier_alignment_decode_encode D,
        VariationMeasureTasteGate_single_carrier_alignment_decode_encode V,
        VariationMeasureTasteGate_single_carrier_alignment_decode_encode A,
        VariationMeasureTasteGate_single_carrier_alignment_decode_encode R,
        VariationMeasureTasteGate_single_carrier_alignment_decode_encode H,
        VariationMeasureTasteGate_single_carrier_alignment_decode_encode C,
        VariationMeasureTasteGate_single_carrier_alignment_decode_encode P,
        VariationMeasureTasteGate_single_carrier_alignment_decode_encode N]

private theorem VariationMeasureTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : VariationMeasureUp} :
    variationMeasureToEventFlow x = variationMeasureToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      variationMeasureFromEventFlow (variationMeasureToEventFlow x) =
        variationMeasureFromEventFlow (variationMeasureToEventFlow y) :=
    congrArg variationMeasureFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (VariationMeasureTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (VariationMeasureTasteGate_single_carrier_alignment_round_trip y)))

private theorem VariationMeasureTasteGate_single_carrier_alignment_fields :
    ∀ x y : VariationMeasureUp, variationMeasureFields x = variationMeasureFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk B1 J1 Pi1 E1 X1 D1 V1 A1 R1 H1 C1 P1 N1 =>
      cases y with
      | mk B2 J2 Pi2 E2 X2 D2 V2 A2 R2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance variationMeasureBHistCarrier : BHistCarrier VariationMeasureUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := variationMeasureToEventFlow
  fromEventFlow := variationMeasureFromEventFlow

instance variationMeasureChapterTasteGate : ChapterTasteGate VariationMeasureUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change variationMeasureFromEventFlow (variationMeasureToEventFlow x) = some x
    exact VariationMeasureTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (VariationMeasureTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance variationMeasureFieldFaithful : FieldFaithful VariationMeasureUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := variationMeasureFields
  field_faithful := VariationMeasureTasteGate_single_carrier_alignment_fields

instance variationMeasureNontrivial :
    BEDC.Meta.TasteGate.Nontrivial VariationMeasureUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨VariationMeasureUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      VariationMeasureUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem VariationMeasureTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate VariationMeasureUp) ∧
      Nonempty (FieldFaithful VariationMeasureUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial VariationMeasureUp) ∧
      (∀ h : BHist, variationMeasureDecodeBHist (variationMeasureEncodeBHist h) = h) ∧
      (∀ x : VariationMeasureUp,
        variationMeasureFromEventFlow (variationMeasureToEventFlow x) = some x) ∧
      (∀ x y : VariationMeasureUp,
        variationMeasureToEventFlow x = variationMeasureToEventFlow y → x = y) ∧
      variationMeasureEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨variationMeasureChapterTasteGate⟩,
      ⟨variationMeasureFieldFaithful⟩,
      ⟨variationMeasureNontrivial⟩,
      VariationMeasureTasteGate_single_carrier_alignment_decode_encode,
      VariationMeasureTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => VariationMeasureTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.VariationMeasureUp
