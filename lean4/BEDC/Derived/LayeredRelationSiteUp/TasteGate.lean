import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LayeredRelationSiteUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LayeredRelationSiteUp : Type where
  | mk :
      (sourceA sourceB relationA relationB refinementChain localityGate relationTransport
        replay transport continuation provenance name : BHist) →
      LayeredRelationSiteUp
  deriving DecidableEq

def layeredRelationSiteEncodeBHist : BHist → RawEvent
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: layeredRelationSiteEncodeBHist h
  | BHist.e1 h => BMark.b1 :: layeredRelationSiteEncodeBHist h

def layeredRelationSiteDecodeBHist : RawEvent → BHist
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (layeredRelationSiteDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (layeredRelationSiteDecodeBHist tail)

private theorem layeredRelationSite_decode_encode_bhist :
    ∀ h : BHist, layeredRelationSiteDecodeBHist (layeredRelationSiteEncodeBHist h) = h := by
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def layeredRelationSiteToEventFlow : LayeredRelationSiteUp → EventFlow
  | LayeredRelationSiteUp.mk sourceA sourceB relationA relationB refinementChain
      localityGate relationTransport replay transport continuation provenance name =>
      [[BMark.b0],
        layeredRelationSiteEncodeBHist sourceA,
        [BMark.b1, BMark.b0],
        layeredRelationSiteEncodeBHist sourceB,
        [BMark.b1, BMark.b1, BMark.b0],
        layeredRelationSiteEncodeBHist relationA,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        layeredRelationSiteEncodeBHist relationB,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        layeredRelationSiteEncodeBHist refinementChain,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        layeredRelationSiteEncodeBHist localityGate,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        layeredRelationSiteEncodeBHist relationTransport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        layeredRelationSiteEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        layeredRelationSiteEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        layeredRelationSiteEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        layeredRelationSiteEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        layeredRelationSiteEncodeBHist name]

private def layeredRelationSiteRawAt : Nat → EventFlow → RawEvent
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => layeredRelationSiteRawAt n rest

private def layeredRelationSiteLengthEq : Nat → EventFlow → Bool
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => layeredRelationSiteLengthEq n rest

def layeredRelationSiteFromEventFlow : EventFlow → Option LayeredRelationSiteUp
  | flow =>
      match layeredRelationSiteLengthEq 24 flow with
      | true =>
          some
            (LayeredRelationSiteUp.mk
              (layeredRelationSiteDecodeBHist (layeredRelationSiteRawAt 1 flow))
              (layeredRelationSiteDecodeBHist (layeredRelationSiteRawAt 3 flow))
              (layeredRelationSiteDecodeBHist (layeredRelationSiteRawAt 5 flow))
              (layeredRelationSiteDecodeBHist (layeredRelationSiteRawAt 7 flow))
              (layeredRelationSiteDecodeBHist (layeredRelationSiteRawAt 9 flow))
              (layeredRelationSiteDecodeBHist (layeredRelationSiteRawAt 11 flow))
              (layeredRelationSiteDecodeBHist (layeredRelationSiteRawAt 13 flow))
              (layeredRelationSiteDecodeBHist (layeredRelationSiteRawAt 15 flow))
              (layeredRelationSiteDecodeBHist (layeredRelationSiteRawAt 17 flow))
              (layeredRelationSiteDecodeBHist (layeredRelationSiteRawAt 19 flow))
              (layeredRelationSiteDecodeBHist (layeredRelationSiteRawAt 21 flow))
              (layeredRelationSiteDecodeBHist (layeredRelationSiteRawAt 23 flow)))
      | false => none

private theorem layeredRelationSite_round_trip :
    ∀ x : LayeredRelationSiteUp,
      layeredRelationSiteFromEventFlow (layeredRelationSiteToEventFlow x) = some x := by
  intro x
  cases x with
  | mk sourceA sourceB relationA relationB refinementChain localityGate relationTransport
      replay transport continuation provenance name =>
      change
        some
          (LayeredRelationSiteUp.mk
            (layeredRelationSiteDecodeBHist (layeredRelationSiteEncodeBHist sourceA))
            (layeredRelationSiteDecodeBHist (layeredRelationSiteEncodeBHist sourceB))
            (layeredRelationSiteDecodeBHist (layeredRelationSiteEncodeBHist relationA))
            (layeredRelationSiteDecodeBHist (layeredRelationSiteEncodeBHist relationB))
            (layeredRelationSiteDecodeBHist
              (layeredRelationSiteEncodeBHist refinementChain))
            (layeredRelationSiteDecodeBHist (layeredRelationSiteEncodeBHist localityGate))
            (layeredRelationSiteDecodeBHist
              (layeredRelationSiteEncodeBHist relationTransport))
            (layeredRelationSiteDecodeBHist (layeredRelationSiteEncodeBHist replay))
            (layeredRelationSiteDecodeBHist (layeredRelationSiteEncodeBHist transport))
            (layeredRelationSiteDecodeBHist (layeredRelationSiteEncodeBHist continuation))
            (layeredRelationSiteDecodeBHist (layeredRelationSiteEncodeBHist provenance))
            (layeredRelationSiteDecodeBHist (layeredRelationSiteEncodeBHist name))) =
          some
            (LayeredRelationSiteUp.mk sourceA sourceB relationA relationB refinementChain
              localityGate relationTransport replay transport continuation provenance name)
      rw [layeredRelationSite_decode_encode_bhist sourceA,
        layeredRelationSite_decode_encode_bhist sourceB,
        layeredRelationSite_decode_encode_bhist relationA,
        layeredRelationSite_decode_encode_bhist relationB,
        layeredRelationSite_decode_encode_bhist refinementChain,
        layeredRelationSite_decode_encode_bhist localityGate,
        layeredRelationSite_decode_encode_bhist relationTransport,
        layeredRelationSite_decode_encode_bhist replay,
        layeredRelationSite_decode_encode_bhist transport,
        layeredRelationSite_decode_encode_bhist continuation,
        layeredRelationSite_decode_encode_bhist provenance,
        layeredRelationSite_decode_encode_bhist name]

private theorem layeredRelationSiteToEventFlow_injective
    {x y : LayeredRelationSiteUp} :
    layeredRelationSiteToEventFlow x = layeredRelationSiteToEventFlow y → x = y := by
  intro heq
  have hread :
      layeredRelationSiteFromEventFlow (layeredRelationSiteToEventFlow x) =
        layeredRelationSiteFromEventFlow (layeredRelationSiteToEventFlow y) :=
    congrArg layeredRelationSiteFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (layeredRelationSite_round_trip x).symm
      (Eq.trans hread (layeredRelationSite_round_trip y)))

instance layeredRelationSiteBHistCarrier : BHistCarrier LayeredRelationSiteUp where
  toEventFlow := layeredRelationSiteToEventFlow
  fromEventFlow := layeredRelationSiteFromEventFlow

instance layeredRelationSiteChapterTasteGate : ChapterTasteGate LayeredRelationSiteUp where
  round_trip := by
    intro x
    change layeredRelationSiteFromEventFlow (layeredRelationSiteToEventFlow x) = some x
    exact layeredRelationSite_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (layeredRelationSiteToEventFlow_injective heq)

instance layeredRelationSiteFieldFaithful : FieldFaithful LayeredRelationSiteUp where
  fields := fun x =>
    match x with
    | LayeredRelationSiteUp.mk sourceA sourceB relationA relationB refinementChain
        localityGate relationTransport replay transport continuation provenance name =>
        [sourceA, sourceB, relationA, relationB, refinementChain, localityGate,
          relationTransport, replay, transport, continuation, provenance, name]
  field_faithful := by
    intro x y h
    cases x with
    | mk sourceA1 sourceB1 relationA1 relationB1 refinementChain1 localityGate1
        relationTransport1 replay1 transport1 continuation1 provenance1 name1 =>
        cases y with
        | mk sourceA2 sourceB2 relationA2 relationB2 refinementChain2 localityGate2
            relationTransport2 replay2 transport2 continuation2 provenance2 name2 =>
            cases h
            rfl

instance layeredRelationSiteNontrivial : Nontrivial LayeredRelationSiteUp where
  witness_pair :=
    ⟨LayeredRelationSiteUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      LayeredRelationSiteUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate LayeredRelationSiteUp :=
  layeredRelationSiteChapterTasteGate

theorem LayeredRelationSiteTasteGate_single_carrier_alignment :
    ChapterTasteGate LayeredRelationSiteUp ∧
      Nonempty (Nontrivial LayeredRelationSiteUp) ∧
        Nonempty (FieldFaithful LayeredRelationSiteUp) ∧
          (∀ h : BHist,
            layeredRelationSiteDecodeBHist (layeredRelationSiteEncodeBHist h) = h) ∧
            (∀ x y : LayeredRelationSiteUp,
              layeredRelationSiteToEventFlow x = layeredRelationSiteToEventFlow y → x = y) := by
  exact
    ⟨layeredRelationSiteChapterTasteGate,
      ⟨layeredRelationSiteNontrivial⟩,
      ⟨layeredRelationSiteFieldFaithful⟩,
      layeredRelationSite_decode_encode_bhist,
      by
        intro x y heq
        exact layeredRelationSiteToEventFlow_injective heq⟩

end BEDC.Derived.LayeredRelationSiteUp
