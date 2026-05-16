import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealityConstrainedTruthCertUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealityConstrainedTruthCertUp : Type where
  | mk :
      (source signature kernelTruth transport stability ledger failure route provenance name :
        BHist) ->
      RealityConstrainedTruthCertUp
  deriving DecidableEq

def realityConstrainedTruthCertEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realityConstrainedTruthCertEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realityConstrainedTruthCertEncodeBHist h

def realityConstrainedTruthCertDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realityConstrainedTruthCertDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realityConstrainedTruthCertDecodeBHist tail)

private theorem realityConstrainedTruthCert_decode_encode_bhist :
    forall h : BHist,
      realityConstrainedTruthCertDecodeBHist
        (realityConstrainedTruthCertEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realityConstrainedTruthCertFields :
    RealityConstrainedTruthCertUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealityConstrainedTruthCertUp.mk source signature kernelTruth transport stability ledger
      failure route provenance name =>
      [source, signature, kernelTruth, transport, stability, ledger, failure, route,
        provenance, name]

def realityConstrainedTruthCertToEventFlow :
    RealityConstrainedTruthCertUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealityConstrainedTruthCertUp.mk source signature kernelTruth transport stability ledger
      failure route provenance name =>
      [[BMark.b0],
        realityConstrainedTruthCertEncodeBHist source,
        [BMark.b1, BMark.b0],
        realityConstrainedTruthCertEncodeBHist signature,
        [BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedTruthCertEncodeBHist kernelTruth,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedTruthCertEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedTruthCertEncodeBHist stability,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedTruthCertEncodeBHist ledger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedTruthCertEncodeBHist failure,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        realityConstrainedTruthCertEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        realityConstrainedTruthCertEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedTruthCertEncodeBHist name]

private def realityConstrainedTruthCertEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      realityConstrainedTruthCertEventAtDefault index rest

def realityConstrainedTruthCertFromEventFlow
    (ef : EventFlow) : Option RealityConstrainedTruthCertUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealityConstrainedTruthCertUp.mk
      (realityConstrainedTruthCertDecodeBHist
        (realityConstrainedTruthCertEventAtDefault 1 ef))
      (realityConstrainedTruthCertDecodeBHist
        (realityConstrainedTruthCertEventAtDefault 3 ef))
      (realityConstrainedTruthCertDecodeBHist
        (realityConstrainedTruthCertEventAtDefault 5 ef))
      (realityConstrainedTruthCertDecodeBHist
        (realityConstrainedTruthCertEventAtDefault 7 ef))
      (realityConstrainedTruthCertDecodeBHist
        (realityConstrainedTruthCertEventAtDefault 9 ef))
      (realityConstrainedTruthCertDecodeBHist
        (realityConstrainedTruthCertEventAtDefault 11 ef))
      (realityConstrainedTruthCertDecodeBHist
        (realityConstrainedTruthCertEventAtDefault 13 ef))
      (realityConstrainedTruthCertDecodeBHist
        (realityConstrainedTruthCertEventAtDefault 15 ef))
      (realityConstrainedTruthCertDecodeBHist
        (realityConstrainedTruthCertEventAtDefault 17 ef))
      (realityConstrainedTruthCertDecodeBHist
        (realityConstrainedTruthCertEventAtDefault 19 ef)))

private theorem realityConstrainedTruthCert_round_trip :
    forall x : RealityConstrainedTruthCertUp,
      realityConstrainedTruthCertFromEventFlow
        (realityConstrainedTruthCertToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source signature kernelTruth transport stability ledger failure route provenance name =>
      change
        some
          (RealityConstrainedTruthCertUp.mk
            (realityConstrainedTruthCertDecodeBHist
              (realityConstrainedTruthCertEncodeBHist source))
            (realityConstrainedTruthCertDecodeBHist
              (realityConstrainedTruthCertEncodeBHist signature))
            (realityConstrainedTruthCertDecodeBHist
              (realityConstrainedTruthCertEncodeBHist kernelTruth))
            (realityConstrainedTruthCertDecodeBHist
              (realityConstrainedTruthCertEncodeBHist transport))
            (realityConstrainedTruthCertDecodeBHist
              (realityConstrainedTruthCertEncodeBHist stability))
            (realityConstrainedTruthCertDecodeBHist
              (realityConstrainedTruthCertEncodeBHist ledger))
            (realityConstrainedTruthCertDecodeBHist
              (realityConstrainedTruthCertEncodeBHist failure))
            (realityConstrainedTruthCertDecodeBHist
              (realityConstrainedTruthCertEncodeBHist route))
            (realityConstrainedTruthCertDecodeBHist
              (realityConstrainedTruthCertEncodeBHist provenance))
            (realityConstrainedTruthCertDecodeBHist
              (realityConstrainedTruthCertEncodeBHist name))) =
          some
            (RealityConstrainedTruthCertUp.mk source signature kernelTruth transport
              stability ledger failure route provenance name)
      rw [realityConstrainedTruthCert_decode_encode_bhist source,
        realityConstrainedTruthCert_decode_encode_bhist signature,
        realityConstrainedTruthCert_decode_encode_bhist kernelTruth,
        realityConstrainedTruthCert_decode_encode_bhist transport,
        realityConstrainedTruthCert_decode_encode_bhist stability,
        realityConstrainedTruthCert_decode_encode_bhist ledger,
        realityConstrainedTruthCert_decode_encode_bhist failure,
        realityConstrainedTruthCert_decode_encode_bhist route,
        realityConstrainedTruthCert_decode_encode_bhist provenance,
        realityConstrainedTruthCert_decode_encode_bhist name]

private theorem realityConstrainedTruthCertToEventFlow_injective
    {x y : RealityConstrainedTruthCertUp} :
    realityConstrainedTruthCertToEventFlow x =
      realityConstrainedTruthCertToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realityConstrainedTruthCertFromEventFlow
          (realityConstrainedTruthCertToEventFlow x) =
        realityConstrainedTruthCertFromEventFlow
          (realityConstrainedTruthCertToEventFlow y) :=
    congrArg realityConstrainedTruthCertFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (realityConstrainedTruthCert_round_trip x).symm
      (Eq.trans hread (realityConstrainedTruthCert_round_trip y)))

private theorem realityConstrainedTruthCert_fields :
    forall x y : RealityConstrainedTruthCertUp,
      realityConstrainedTruthCertFields x =
        realityConstrainedTruthCertFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk source1 signature1 kernelTruth1 transport1 stability1 ledger1 failure1 route1
      provenance1 name1 =>
      cases y with
      | mk source2 signature2 kernelTruth2 transport2 stability2 ledger2 failure2 route2
          provenance2 name2 =>
          cases hfields
          rfl

instance realityConstrainedTruthCertBHistCarrier :
    BHistCarrier RealityConstrainedTruthCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realityConstrainedTruthCertToEventFlow
  fromEventFlow := realityConstrainedTruthCertFromEventFlow

instance realityConstrainedTruthCertChapterTasteGate :
    ChapterTasteGate RealityConstrainedTruthCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realityConstrainedTruthCertFromEventFlow
      (realityConstrainedTruthCertToEventFlow x) = some x
    exact realityConstrainedTruthCert_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realityConstrainedTruthCertToEventFlow_injective heq)

instance realityConstrainedTruthCertFieldFaithful :
    FieldFaithful RealityConstrainedTruthCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realityConstrainedTruthCertFields
  field_faithful := realityConstrainedTruthCert_fields

instance realityConstrainedTruthCertNontrivial :
    Nontrivial RealityConstrainedTruthCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealityConstrainedTruthCertUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealityConstrainedTruthCertUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealityConstrainedTruthCertUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realityConstrainedTruthCertChapterTasteGate

end BEDC.Derived.RealityConstrainedTruthCertUp.TasteGate

namespace BEDC.Derived.RealityConstrainedTruthCertUp

def taste_gate :
    BEDC.Meta.TasteGate.ChapterTasteGate TasteGate.RealityConstrainedTruthCertUp :=
  -- BEDC touchpoint anchor: BHist BMark
  TasteGate.taste_gate

end BEDC.Derived.RealityConstrainedTruthCertUp
