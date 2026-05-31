import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BoundedCauchyIntervalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BoundedCauchyIntervalUp : Type where
  | mk (B S R D L F E H C P N : BHist) : BoundedCauchyIntervalUp
  deriving DecidableEq

def boundedCauchyIntervalFields : BoundedCauchyIntervalUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BoundedCauchyIntervalUp.mk B S R D L F E H C P N => [B, S, R, D, L, F, E, H, C, P, N]

def boundedCauchyIntervalEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: boundedCauchyIntervalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: boundedCauchyIntervalEncodeBHist h

def boundedCauchyIntervalDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (boundedCauchyIntervalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (boundedCauchyIntervalDecodeBHist tail)

private theorem BoundedCauchyIntervalTasteGate_single_carrier_alignment_decode :
    forall h : BHist, boundedCauchyIntervalDecodeBHist (boundedCauchyIntervalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def boundedCauchyIntervalToEventFlow : BoundedCauchyIntervalUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (boundedCauchyIntervalFields x).map boundedCauchyIntervalEncodeBHist

private def boundedCauchyIntervalRawAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _ => event
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => boundedCauchyIntervalRawAt n rest

def boundedCauchyIntervalFromEventFlow (flow : EventFlow) : Option BoundedCauchyIntervalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BoundedCauchyIntervalUp.mk
      (boundedCauchyIntervalDecodeBHist (boundedCauchyIntervalRawAt 0 flow))
      (boundedCauchyIntervalDecodeBHist (boundedCauchyIntervalRawAt 1 flow))
      (boundedCauchyIntervalDecodeBHist (boundedCauchyIntervalRawAt 2 flow))
      (boundedCauchyIntervalDecodeBHist (boundedCauchyIntervalRawAt 3 flow))
      (boundedCauchyIntervalDecodeBHist (boundedCauchyIntervalRawAt 4 flow))
      (boundedCauchyIntervalDecodeBHist (boundedCauchyIntervalRawAt 5 flow))
      (boundedCauchyIntervalDecodeBHist (boundedCauchyIntervalRawAt 6 flow))
      (boundedCauchyIntervalDecodeBHist (boundedCauchyIntervalRawAt 7 flow))
      (boundedCauchyIntervalDecodeBHist (boundedCauchyIntervalRawAt 8 flow))
      (boundedCauchyIntervalDecodeBHist (boundedCauchyIntervalRawAt 9 flow))
      (boundedCauchyIntervalDecodeBHist (boundedCauchyIntervalRawAt 10 flow)))

private theorem BoundedCauchyIntervalTasteGate_single_carrier_alignment_round_trip
    (x : BoundedCauchyIntervalUp) :
    boundedCauchyIntervalFromEventFlow (boundedCauchyIntervalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk B S R D L F E H C P N =>
      change
        some
          (BoundedCauchyIntervalUp.mk
            (boundedCauchyIntervalDecodeBHist (boundedCauchyIntervalEncodeBHist B))
            (boundedCauchyIntervalDecodeBHist (boundedCauchyIntervalEncodeBHist S))
            (boundedCauchyIntervalDecodeBHist (boundedCauchyIntervalEncodeBHist R))
            (boundedCauchyIntervalDecodeBHist (boundedCauchyIntervalEncodeBHist D))
            (boundedCauchyIntervalDecodeBHist (boundedCauchyIntervalEncodeBHist L))
            (boundedCauchyIntervalDecodeBHist (boundedCauchyIntervalEncodeBHist F))
            (boundedCauchyIntervalDecodeBHist (boundedCauchyIntervalEncodeBHist E))
            (boundedCauchyIntervalDecodeBHist (boundedCauchyIntervalEncodeBHist H))
            (boundedCauchyIntervalDecodeBHist (boundedCauchyIntervalEncodeBHist C))
            (boundedCauchyIntervalDecodeBHist (boundedCauchyIntervalEncodeBHist P))
            (boundedCauchyIntervalDecodeBHist (boundedCauchyIntervalEncodeBHist N))) =
          some (BoundedCauchyIntervalUp.mk B S R D L F E H C P N)
      rw [BoundedCauchyIntervalTasteGate_single_carrier_alignment_decode B,
        BoundedCauchyIntervalTasteGate_single_carrier_alignment_decode S,
        BoundedCauchyIntervalTasteGate_single_carrier_alignment_decode R,
        BoundedCauchyIntervalTasteGate_single_carrier_alignment_decode D,
        BoundedCauchyIntervalTasteGate_single_carrier_alignment_decode L,
        BoundedCauchyIntervalTasteGate_single_carrier_alignment_decode F,
        BoundedCauchyIntervalTasteGate_single_carrier_alignment_decode E,
        BoundedCauchyIntervalTasteGate_single_carrier_alignment_decode H,
        BoundedCauchyIntervalTasteGate_single_carrier_alignment_decode C,
        BoundedCauchyIntervalTasteGate_single_carrier_alignment_decode P,
        BoundedCauchyIntervalTasteGate_single_carrier_alignment_decode N]

private theorem BoundedCauchyIntervalTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BoundedCauchyIntervalUp} :
    boundedCauchyIntervalToEventFlow x = boundedCauchyIntervalToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      boundedCauchyIntervalFromEventFlow (boundedCauchyIntervalToEventFlow x) =
        boundedCauchyIntervalFromEventFlow (boundedCauchyIntervalToEventFlow y) :=
    congrArg boundedCauchyIntervalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BoundedCauchyIntervalTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (BoundedCauchyIntervalTasteGate_single_carrier_alignment_round_trip y)))

private theorem BoundedCauchyIntervalTasteGate_single_carrier_alignment_fields_faithful :
    forall x y : BoundedCauchyIntervalUp, boundedCauchyIntervalFields x = boundedCauchyIntervalFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk Ba Sa Ra Da La Fa Ea Ha Ca Pa Na =>
      cases y with
      | mk Bb Sb Rb Db Lb Fb Eb Hb Cb Pb Nb =>
          cases hfields
          rfl

instance boundedCauchyIntervalBHistCarrier : BHistCarrier BoundedCauchyIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := boundedCauchyIntervalToEventFlow
  fromEventFlow := boundedCauchyIntervalFromEventFlow

instance boundedCauchyIntervalChapterTasteGate : ChapterTasteGate BoundedCauchyIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change boundedCauchyIntervalFromEventFlow (boundedCauchyIntervalToEventFlow x) = some x
    exact BoundedCauchyIntervalTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BoundedCauchyIntervalTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance boundedCauchyIntervalFieldFaithful : FieldFaithful BoundedCauchyIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := boundedCauchyIntervalFields
  field_faithful := BoundedCauchyIntervalTasteGate_single_carrier_alignment_fields_faithful

instance boundedCauchyIntervalNontrivial : Nontrivial BoundedCauchyIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BoundedCauchyIntervalUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      BoundedCauchyIntervalUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

theorem BoundedCauchyIntervalTasteGate_single_carrier_alignment :
    (∀ h : BHist, boundedCauchyIntervalDecodeBHist (boundedCauchyIntervalEncodeBHist h) = h) ∧
      (∀ x : BoundedCauchyIntervalUp,
        boundedCauchyIntervalFromEventFlow (boundedCauchyIntervalToEventFlow x) = some x) ∧
      (∀ x y : BoundedCauchyIntervalUp,
        boundedCauchyIntervalToEventFlow x = boundedCauchyIntervalToEventFlow y → x = y) ∧
      Nonempty (FieldFaithful BoundedCauchyIntervalUp) ∧
      Nonempty (ChapterTasteGate BoundedCauchyIntervalUp) ∧
      boundedCauchyIntervalEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨BoundedCauchyIntervalTasteGate_single_carrier_alignment_decode,
      BoundedCauchyIntervalTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq => BoundedCauchyIntervalTasteGate_single_carrier_alignment_toEventFlow_injective heq,
      ⟨boundedCauchyIntervalFieldFaithful⟩, ⟨boundedCauchyIntervalChapterTasteGate⟩, rfl⟩

end BEDC.Derived.BoundedCauchyIntervalUp
