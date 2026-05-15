import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DigestLoopRefusalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DigestLoopRefusalUp : Type where
  | mk :
      (visibleDigest fiberLedger farEndSocket loopRefusal exactnessRefusal transport replay
        provenance nameCert : BHist) →
      DigestLoopRefusalUp
  deriving DecidableEq

def digestLoopRefusalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: digestLoopRefusalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: digestLoopRefusalEncodeBHist h

def digestLoopRefusalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (digestLoopRefusalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (digestLoopRefusalDecodeBHist tail)

private theorem digestLoopRefusalDecode_encode_bhist :
    ∀ h : BHist, digestLoopRefusalDecodeBHist (digestLoopRefusalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem digestLoopRefusal_mk_congr
    {visibleDigest visibleDigest' fiberLedger fiberLedger' farEndSocket farEndSocket'
      loopRefusal loopRefusal' exactnessRefusal exactnessRefusal' transport transport'
      replay replay' provenance provenance' nameCert nameCert' : BHist}
    (hVisibleDigest : visibleDigest' = visibleDigest)
    (hFiberLedger : fiberLedger' = fiberLedger)
    (hFarEndSocket : farEndSocket' = farEndSocket)
    (hLoopRefusal : loopRefusal' = loopRefusal)
    (hExactnessRefusal : exactnessRefusal' = exactnessRefusal)
    (hTransport : transport' = transport)
    (hReplay : replay' = replay)
    (hProvenance : provenance' = provenance)
    (hNameCert : nameCert' = nameCert) :
    DigestLoopRefusalUp.mk visibleDigest' fiberLedger' farEndSocket' loopRefusal'
        exactnessRefusal' transport' replay' provenance' nameCert' =
      DigestLoopRefusalUp.mk visibleDigest fiberLedger farEndSocket loopRefusal
        exactnessRefusal transport replay provenance nameCert := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hVisibleDigest
  cases hFiberLedger
  cases hFarEndSocket
  cases hLoopRefusal
  cases hExactnessRefusal
  cases hTransport
  cases hReplay
  cases hProvenance
  cases hNameCert
  rfl

def digestLoopRefusalFields : DigestLoopRefusalUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DigestLoopRefusalUp.mk visibleDigest fiberLedger farEndSocket loopRefusal
      exactnessRefusal transport replay provenance nameCert =>
      [visibleDigest, fiberLedger, farEndSocket, loopRefusal, exactnessRefusal, transport,
        replay, provenance, nameCert]

def digestLoopRefusalToEventFlow : DigestLoopRefusalUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (digestLoopRefusalFields x).map digestLoopRefusalEncodeBHist

private def digestLoopRefusalEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => digestLoopRefusalEventAtDefault index rest

def digestLoopRefusalFromEventFlow (ef : EventFlow) : Option DigestLoopRefusalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DigestLoopRefusalUp.mk
      (digestLoopRefusalDecodeBHist (digestLoopRefusalEventAtDefault 0 ef))
      (digestLoopRefusalDecodeBHist (digestLoopRefusalEventAtDefault 1 ef))
      (digestLoopRefusalDecodeBHist (digestLoopRefusalEventAtDefault 2 ef))
      (digestLoopRefusalDecodeBHist (digestLoopRefusalEventAtDefault 3 ef))
      (digestLoopRefusalDecodeBHist (digestLoopRefusalEventAtDefault 4 ef))
      (digestLoopRefusalDecodeBHist (digestLoopRefusalEventAtDefault 5 ef))
      (digestLoopRefusalDecodeBHist (digestLoopRefusalEventAtDefault 6 ef))
      (digestLoopRefusalDecodeBHist (digestLoopRefusalEventAtDefault 7 ef))
      (digestLoopRefusalDecodeBHist (digestLoopRefusalEventAtDefault 8 ef)))

private theorem digestLoopRefusal_round_trip :
    ∀ x : DigestLoopRefusalUp,
      digestLoopRefusalFromEventFlow (digestLoopRefusalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk visibleDigest fiberLedger farEndSocket loopRefusal exactnessRefusal transport replay
      provenance nameCert =>
      change
        some
          (DigestLoopRefusalUp.mk
            (digestLoopRefusalDecodeBHist (digestLoopRefusalEncodeBHist visibleDigest))
            (digestLoopRefusalDecodeBHist (digestLoopRefusalEncodeBHist fiberLedger))
            (digestLoopRefusalDecodeBHist (digestLoopRefusalEncodeBHist farEndSocket))
            (digestLoopRefusalDecodeBHist (digestLoopRefusalEncodeBHist loopRefusal))
            (digestLoopRefusalDecodeBHist (digestLoopRefusalEncodeBHist exactnessRefusal))
            (digestLoopRefusalDecodeBHist (digestLoopRefusalEncodeBHist transport))
            (digestLoopRefusalDecodeBHist (digestLoopRefusalEncodeBHist replay))
            (digestLoopRefusalDecodeBHist (digestLoopRefusalEncodeBHist provenance))
            (digestLoopRefusalDecodeBHist (digestLoopRefusalEncodeBHist nameCert))) =
          some
            (DigestLoopRefusalUp.mk visibleDigest fiberLedger farEndSocket loopRefusal
              exactnessRefusal transport replay provenance nameCert)
      exact
        congrArg some
          (digestLoopRefusal_mk_congr
            (digestLoopRefusalDecode_encode_bhist visibleDigest)
            (digestLoopRefusalDecode_encode_bhist fiberLedger)
            (digestLoopRefusalDecode_encode_bhist farEndSocket)
            (digestLoopRefusalDecode_encode_bhist loopRefusal)
            (digestLoopRefusalDecode_encode_bhist exactnessRefusal)
            (digestLoopRefusalDecode_encode_bhist transport)
            (digestLoopRefusalDecode_encode_bhist replay)
            (digestLoopRefusalDecode_encode_bhist provenance)
            (digestLoopRefusalDecode_encode_bhist nameCert))

private theorem digestLoopRefusalToEventFlow_injective {x y : DigestLoopRefusalUp} :
    digestLoopRefusalToEventFlow x = digestLoopRefusalToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      digestLoopRefusalFromEventFlow (digestLoopRefusalToEventFlow x) =
        digestLoopRefusalFromEventFlow (digestLoopRefusalToEventFlow y) :=
    congrArg digestLoopRefusalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (digestLoopRefusal_round_trip x).symm
      (Eq.trans hread (digestLoopRefusal_round_trip y)))

private theorem digestLoopRefusal_fields_faithful :
    ∀ x y : DigestLoopRefusalUp, digestLoopRefusalFields x = digestLoopRefusalFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk visibleDigest₁ fiberLedger₁ farEndSocket₁ loopRefusal₁ exactnessRefusal₁ transport₁
      replay₁ provenance₁ nameCert₁ =>
      cases y with
      | mk visibleDigest₂ fiberLedger₂ farEndSocket₂ loopRefusal₂ exactnessRefusal₂ transport₂
          replay₂ provenance₂ nameCert₂ =>
          cases hfields
          rfl

instance digestLoopRefusalBHistCarrier : BHistCarrier DigestLoopRefusalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := digestLoopRefusalToEventFlow
  fromEventFlow := digestLoopRefusalFromEventFlow

instance digestLoopRefusalChapterTasteGate : ChapterTasteGate DigestLoopRefusalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change digestLoopRefusalFromEventFlow (digestLoopRefusalToEventFlow x) = some x
    exact digestLoopRefusal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (digestLoopRefusalToEventFlow_injective heq)

instance digestLoopRefusalFieldFaithful : FieldFaithful DigestLoopRefusalUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := digestLoopRefusalFields
  field_faithful := digestLoopRefusal_fields_faithful

instance digestLoopRefusalNontrivial : Nontrivial DigestLoopRefusalUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DigestLoopRefusalUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DigestLoopRefusalUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DigestLoopRefusalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  digestLoopRefusalChapterTasteGate

theorem DigestLoopRefusalTasteGate_single_carrier_alignment :
    (∀ h : BHist, digestLoopRefusalDecodeBHist (digestLoopRefusalEncodeBHist h) = h) ∧
      (∀ x : DigestLoopRefusalUp,
        digestLoopRefusalFromEventFlow (digestLoopRefusalToEventFlow x) = some x) ∧
        (∀ x y : DigestLoopRefusalUp,
          digestLoopRefusalToEventFlow x = digestLoopRefusalToEventFlow y → x = y) ∧
          digestLoopRefusalEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact digestLoopRefusalDecode_encode_bhist
  · constructor
    · exact digestLoopRefusal_round_trip
    · constructor
      · intro x y heq
        exact digestLoopRefusalToEventFlow_injective heq
      · rfl

end BEDC.Derived.DigestLoopRefusalUp
