import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ObservationFiberDigestUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ObservationFiberDigestUp : Type where
  | mk (digest fiber gap signature provenance name farEnd transport replay : BHist) :
      ObservationFiberDigestUp
  deriving DecidableEq

def observationFiberDigestEncodeBHist : BHist → RawEvent
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: observationFiberDigestEncodeBHist h
  | BHist.e1 h => BMark.b1 :: observationFiberDigestEncodeBHist h

def observationFiberDigestDecodeBHist : RawEvent → BHist
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (observationFiberDigestDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (observationFiberDigestDecodeBHist tail)

private theorem observationFiberDigestDecode_encode_bhist :
    ∀ h : BHist,
      observationFiberDigestDecodeBHist (observationFiberDigestEncodeBHist h) = h := by
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def observationFiberDigestFields : ObservationFiberDigestUp → List BHist
  | ObservationFiberDigestUp.mk digest fiber gap signature provenance name farEnd transport
      replay =>
      [digest, fiber, gap, signature, provenance, name, farEnd, transport, replay]

def observationFiberDigestToEventFlow : ObservationFiberDigestUp → EventFlow
  | x => (observationFiberDigestFields x).map observationFiberDigestEncodeBHist

private def observationFiberDigestEventAtDefault : Nat → EventFlow → RawEvent
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => observationFiberDigestEventAtDefault index rest

def observationFiberDigestFromEventFlow (ef : EventFlow) : Option ObservationFiberDigestUp :=
  some
    (ObservationFiberDigestUp.mk
      (observationFiberDigestDecodeBHist (observationFiberDigestEventAtDefault 0 ef))
      (observationFiberDigestDecodeBHist (observationFiberDigestEventAtDefault 1 ef))
      (observationFiberDigestDecodeBHist (observationFiberDigestEventAtDefault 2 ef))
      (observationFiberDigestDecodeBHist (observationFiberDigestEventAtDefault 3 ef))
      (observationFiberDigestDecodeBHist (observationFiberDigestEventAtDefault 4 ef))
      (observationFiberDigestDecodeBHist (observationFiberDigestEventAtDefault 5 ef))
      (observationFiberDigestDecodeBHist (observationFiberDigestEventAtDefault 6 ef))
      (observationFiberDigestDecodeBHist (observationFiberDigestEventAtDefault 7 ef))
      (observationFiberDigestDecodeBHist (observationFiberDigestEventAtDefault 8 ef)))

private theorem observationFiberDigest_mk_congr
    {digest digest' fiber fiber' gap gap' signature signature' provenance provenance'
      name name' farEnd farEnd' transport transport' replay replay' : BHist}
    (hDigest : digest' = digest)
    (hFiber : fiber' = fiber)
    (hGap : gap' = gap)
    (hSignature : signature' = signature)
    (hProvenance : provenance' = provenance)
    (hName : name' = name)
    (hFarEnd : farEnd' = farEnd)
    (hTransport : transport' = transport)
    (hReplay : replay' = replay) :
    ObservationFiberDigestUp.mk digest' fiber' gap' signature' provenance' name' farEnd'
        transport' replay' =
      ObservationFiberDigestUp.mk digest fiber gap signature provenance name farEnd transport
        replay := by
  cases hDigest
  cases hFiber
  cases hGap
  cases hSignature
  cases hProvenance
  cases hName
  cases hFarEnd
  cases hTransport
  cases hReplay
  rfl

private theorem observationFiberDigest_round_trip :
    ∀ x : ObservationFiberDigestUp,
      observationFiberDigestFromEventFlow (observationFiberDigestToEventFlow x) = some x := by
  intro x
  cases x with
  | mk digest fiber gap signature provenance name farEnd transport replay =>
      change
        some
          (ObservationFiberDigestUp.mk
            (observationFiberDigestDecodeBHist
              (observationFiberDigestEncodeBHist digest))
            (observationFiberDigestDecodeBHist
              (observationFiberDigestEncodeBHist fiber))
            (observationFiberDigestDecodeBHist
              (observationFiberDigestEncodeBHist gap))
            (observationFiberDigestDecodeBHist
              (observationFiberDigestEncodeBHist signature))
            (observationFiberDigestDecodeBHist
              (observationFiberDigestEncodeBHist provenance))
            (observationFiberDigestDecodeBHist
              (observationFiberDigestEncodeBHist name))
            (observationFiberDigestDecodeBHist
              (observationFiberDigestEncodeBHist farEnd))
            (observationFiberDigestDecodeBHist
              (observationFiberDigestEncodeBHist transport))
            (observationFiberDigestDecodeBHist
              (observationFiberDigestEncodeBHist replay))) =
          some
            (ObservationFiberDigestUp.mk digest fiber gap signature provenance name farEnd
              transport replay)
      exact
        congrArg some
          (observationFiberDigest_mk_congr
            (observationFiberDigestDecode_encode_bhist digest)
            (observationFiberDigestDecode_encode_bhist fiber)
            (observationFiberDigestDecode_encode_bhist gap)
            (observationFiberDigestDecode_encode_bhist signature)
            (observationFiberDigestDecode_encode_bhist provenance)
            (observationFiberDigestDecode_encode_bhist name)
            (observationFiberDigestDecode_encode_bhist farEnd)
            (observationFiberDigestDecode_encode_bhist transport)
            (observationFiberDigestDecode_encode_bhist replay))

private theorem observationFiberDigestToEventFlow_injective {x y : ObservationFiberDigestUp} :
    observationFiberDigestToEventFlow x = observationFiberDigestToEventFlow y → x = y := by
  intro heq
  have hread :
      observationFiberDigestFromEventFlow (observationFiberDigestToEventFlow x) =
        observationFiberDigestFromEventFlow (observationFiberDigestToEventFlow y) :=
    congrArg observationFiberDigestFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (observationFiberDigest_round_trip x).symm
      (Eq.trans hread (observationFiberDigest_round_trip y)))

private theorem observationFiberDigest_fields_faithful :
    ∀ x y : ObservationFiberDigestUp,
      observationFiberDigestFields x = observationFiberDigestFields y → x = y := by
  intro x y hfields
  cases x with
  | mk digest₁ fiber₁ gap₁ signature₁ provenance₁ name₁ farEnd₁ transport₁ replay₁ =>
      cases y with
      | mk digest₂ fiber₂ gap₂ signature₂ provenance₂ name₂ farEnd₂ transport₂ replay₂ =>
          cases hfields
          rfl

instance observationFiberDigestBHistCarrier :
    BHistCarrier ObservationFiberDigestUp where
  toEventFlow := observationFiberDigestToEventFlow
  fromEventFlow := observationFiberDigestFromEventFlow

instance observationFiberDigestChapterTasteGate :
    ChapterTasteGate ObservationFiberDigestUp where
  round_trip := by
    intro x
    change
      observationFiberDigestFromEventFlow (observationFiberDigestToEventFlow x) = some x
    exact observationFiberDigest_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (observationFiberDigestToEventFlow_injective heq)

instance observationFiberDigestFieldFaithful :
    FieldFaithful ObservationFiberDigestUp where
  fields := observationFiberDigestFields
  field_faithful := observationFiberDigest_fields_faithful

instance observationFiberDigestNontrivial : Nontrivial ObservationFiberDigestUp where
  witness_pair :=
    ⟨ObservationFiberDigestUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ObservationFiberDigestUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ObservationFiberDigestUp :=
  observationFiberDigestChapterTasteGate

theorem ObservationFiberDigestTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate ObservationFiberDigestUp) ∧
      Nonempty (FieldFaithful ObservationFiberDigestUp) ∧
        Nonempty (Nontrivial ObservationFiberDigestUp) ∧
          (∀ x : ObservationFiberDigestUp,
            observationFiberDigestFromEventFlow (observationFiberDigestToEventFlow x) =
              some x) ∧
            (∀ x y : ObservationFiberDigestUp,
              observationFiberDigestToEventFlow x = observationFiberDigestToEventFlow y →
                x = y) ∧
              observationFiberDigestEncodeBHist BHist.Empty = ([] : RawEvent) := by
  constructor
  · exact ⟨observationFiberDigestChapterTasteGate⟩
  · constructor
    · exact ⟨observationFiberDigestFieldFaithful⟩
    · constructor
      · exact ⟨observationFiberDigestNontrivial⟩
      · constructor
        · exact observationFiberDigest_round_trip
        · constructor
          · intro x y heq
            exact observationFiberDigestToEventFlow_injective heq
          · rfl

end BEDC.Derived.ObservationFiberDigestUp
