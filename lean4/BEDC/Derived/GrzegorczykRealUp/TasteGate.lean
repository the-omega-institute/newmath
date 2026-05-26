import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.GrzegorczykRealUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive GrzegorczykRealUp : Type where
  | mk
      (approximant stream dyadic readback realSeal transport replay provenance nameRow :
        BHist) : GrzegorczykRealUp
  deriving DecidableEq

def grzegorczykRealEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: grzegorczykRealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: grzegorczykRealEncodeBHist h

def grzegorczykRealDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (grzegorczykRealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (grzegorczykRealDecodeBHist tail)

private theorem GrzegorczykRealTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist, grzegorczykRealDecodeBHist (grzegorczykRealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def grzegorczykRealFields : GrzegorczykRealUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | GrzegorczykRealUp.mk approximant stream dyadic readback realSeal transport replay
      provenance nameRow =>
      [approximant, stream, dyadic, readback, realSeal, transport, replay, provenance,
        nameRow]

def grzegorczykRealToEventFlow : GrzegorczykRealUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (grzegorczykRealFields x).map grzegorczykRealEncodeBHist

def grzegorczykRealEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => grzegorczykRealEventAt index rest

def grzegorczykRealFromEventFlow : EventFlow -> Option GrzegorczykRealUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      some
        (GrzegorczykRealUp.mk
          (grzegorczykRealDecodeBHist (grzegorczykRealEventAt 0 flow))
          (grzegorczykRealDecodeBHist (grzegorczykRealEventAt 1 flow))
          (grzegorczykRealDecodeBHist (grzegorczykRealEventAt 2 flow))
          (grzegorczykRealDecodeBHist (grzegorczykRealEventAt 3 flow))
          (grzegorczykRealDecodeBHist (grzegorczykRealEventAt 4 flow))
          (grzegorczykRealDecodeBHist (grzegorczykRealEventAt 5 flow))
          (grzegorczykRealDecodeBHist (grzegorczykRealEventAt 6 flow))
          (grzegorczykRealDecodeBHist (grzegorczykRealEventAt 7 flow))
          (grzegorczykRealDecodeBHist (grzegorczykRealEventAt 8 flow)))

private theorem GrzegorczykRealTasteGate_single_carrier_alignment_round_trip :
    forall x : GrzegorczykRealUp,
      grzegorczykRealFromEventFlow (grzegorczykRealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk approximant stream dyadic readback realSeal transport replay provenance nameRow =>
      change
        some
          (GrzegorczykRealUp.mk
            (grzegorczykRealDecodeBHist (grzegorczykRealEncodeBHist approximant))
            (grzegorczykRealDecodeBHist (grzegorczykRealEncodeBHist stream))
            (grzegorczykRealDecodeBHist (grzegorczykRealEncodeBHist dyadic))
            (grzegorczykRealDecodeBHist (grzegorczykRealEncodeBHist readback))
            (grzegorczykRealDecodeBHist (grzegorczykRealEncodeBHist realSeal))
            (grzegorczykRealDecodeBHist (grzegorczykRealEncodeBHist transport))
            (grzegorczykRealDecodeBHist (grzegorczykRealEncodeBHist replay))
            (grzegorczykRealDecodeBHist (grzegorczykRealEncodeBHist provenance))
            (grzegorczykRealDecodeBHist (grzegorczykRealEncodeBHist nameRow))) =
          some
            (GrzegorczykRealUp.mk approximant stream dyadic readback realSeal transport
              replay provenance nameRow)
      rw [GrzegorczykRealTasteGate_single_carrier_alignment_decode_encode approximant,
        GrzegorczykRealTasteGate_single_carrier_alignment_decode_encode stream,
        GrzegorczykRealTasteGate_single_carrier_alignment_decode_encode dyadic,
        GrzegorczykRealTasteGate_single_carrier_alignment_decode_encode readback,
        GrzegorczykRealTasteGate_single_carrier_alignment_decode_encode realSeal,
        GrzegorczykRealTasteGate_single_carrier_alignment_decode_encode transport,
        GrzegorczykRealTasteGate_single_carrier_alignment_decode_encode replay,
        GrzegorczykRealTasteGate_single_carrier_alignment_decode_encode provenance,
        GrzegorczykRealTasteGate_single_carrier_alignment_decode_encode nameRow]

private theorem grzegorczykRealToEventFlow_injective {x y : GrzegorczykRealUp} :
    grzegorczykRealToEventFlow x = grzegorczykRealToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      grzegorczykRealFromEventFlow (grzegorczykRealToEventFlow x) =
        grzegorczykRealFromEventFlow (grzegorczykRealToEventFlow y) :=
    congrArg grzegorczykRealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (GrzegorczykRealTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (GrzegorczykRealTasteGate_single_carrier_alignment_round_trip y)))

private theorem GrzegorczykRealTasteGate_single_carrier_alignment_fields_faithful :
    forall x y : GrzegorczykRealUp, grzegorczykRealFields x = grzegorczykRealFields y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk approximant1 stream1 dyadic1 readback1 realSeal1 transport1 replay1 provenance1
      nameRow1 =>
      cases y with
      | mk approximant2 stream2 dyadic2 readback2 realSeal2 transport2 replay2 provenance2
          nameRow2 =>
          cases hfields
          rfl

instance grzegorczykRealBHistCarrier : BHistCarrier GrzegorczykRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := grzegorczykRealToEventFlow
  fromEventFlow := grzegorczykRealFromEventFlow

instance grzegorczykRealChapterTasteGate : ChapterTasteGate GrzegorczykRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change grzegorczykRealFromEventFlow (grzegorczykRealToEventFlow x) = some x
    exact GrzegorczykRealTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (grzegorczykRealToEventFlow_injective heq)

instance grzegorczykRealFieldFaithful : FieldFaithful GrzegorczykRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := grzegorczykRealFields
  field_faithful := GrzegorczykRealTasteGate_single_carrier_alignment_fields_faithful

instance grzegorczykRealNontrivial :
    BEDC.Meta.TasteGate.Nontrivial GrzegorczykRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨GrzegorczykRealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      GrzegorczykRealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate GrzegorczykRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  grzegorczykRealChapterTasteGate

theorem GrzegorczykRealTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate GrzegorczykRealUp) ∧
      Nonempty (FieldFaithful GrzegorczykRealUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial GrzegorczykRealUp) ∧
          (∀ h : BHist, grzegorczykRealDecodeBHist (grzegorczykRealEncodeBHist h) = h) ∧
            (∀ x : GrzegorczykRealUp,
              grzegorczykRealFromEventFlow (grzegorczykRealToEventFlow x) = some x) ∧
              (∀ x y : GrzegorczykRealUp,
                grzegorczykRealToEventFlow x = grzegorczykRealToEventFlow y -> x = y) ∧
                grzegorczykRealEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨grzegorczykRealChapterTasteGate⟩,
      ⟨grzegorczykRealFieldFaithful⟩,
      ⟨grzegorczykRealNontrivial⟩,
      GrzegorczykRealTasteGate_single_carrier_alignment_decode_encode,
      GrzegorczykRealTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => grzegorczykRealToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.GrzegorczykRealUp.TasteGate
