import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CertificateTruthBranchBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CertificateTruthBranchBoundaryUp : Type where
  | mk
      (query assumption refutation decision refusal ledger transport continuation provenance
        localName : BHist) :
      CertificateTruthBranchBoundaryUp
  deriving DecidableEq

def certificateTruthBranchBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: certificateTruthBranchBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: certificateTruthBranchBoundaryEncodeBHist h

def certificateTruthBranchBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (certificateTruthBranchBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (certificateTruthBranchBoundaryDecodeBHist tail)

private theorem certificateTruthBranchBoundaryDecode_encode_bhist :
    ∀ h : BHist,
      certificateTruthBranchBoundaryDecodeBHist
        (certificateTruthBranchBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def certificateTruthBranchBoundaryFields :
    CertificateTruthBranchBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CertificateTruthBranchBoundaryUp.mk query assumption refutation decision refusal ledger
      transport continuation provenance localName =>
      [query, assumption, refutation, decision, refusal, ledger, transport, continuation,
        provenance, localName]

def certificateTruthBranchBoundaryToEventFlow :
    CertificateTruthBranchBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (certificateTruthBranchBoundaryFields x).map certificateTruthBranchBoundaryEncodeBHist

private def certificateTruthBranchBoundaryEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      certificateTruthBranchBoundaryEventAtDefault index rest

def certificateTruthBranchBoundaryFromEventFlow
    (ef : EventFlow) : Option CertificateTruthBranchBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CertificateTruthBranchBoundaryUp.mk
      (certificateTruthBranchBoundaryDecodeBHist
        (certificateTruthBranchBoundaryEventAtDefault 0 ef))
      (certificateTruthBranchBoundaryDecodeBHist
        (certificateTruthBranchBoundaryEventAtDefault 1 ef))
      (certificateTruthBranchBoundaryDecodeBHist
        (certificateTruthBranchBoundaryEventAtDefault 2 ef))
      (certificateTruthBranchBoundaryDecodeBHist
        (certificateTruthBranchBoundaryEventAtDefault 3 ef))
      (certificateTruthBranchBoundaryDecodeBHist
        (certificateTruthBranchBoundaryEventAtDefault 4 ef))
      (certificateTruthBranchBoundaryDecodeBHist
        (certificateTruthBranchBoundaryEventAtDefault 5 ef))
      (certificateTruthBranchBoundaryDecodeBHist
        (certificateTruthBranchBoundaryEventAtDefault 6 ef))
      (certificateTruthBranchBoundaryDecodeBHist
        (certificateTruthBranchBoundaryEventAtDefault 7 ef))
      (certificateTruthBranchBoundaryDecodeBHist
        (certificateTruthBranchBoundaryEventAtDefault 8 ef))
      (certificateTruthBranchBoundaryDecodeBHist
        (certificateTruthBranchBoundaryEventAtDefault 9 ef)))

private theorem certificateTruthBranchBoundary_mk_congr
    {query query' assumption assumption' refutation refutation' decision decision'
      refusal refusal' ledger ledger' transport transport' continuation continuation'
      provenance provenance' localName localName' : BHist}
    (hQuery : query' = query)
    (hAssumption : assumption' = assumption)
    (hRefutation : refutation' = refutation)
    (hDecision : decision' = decision)
    (hRefusal : refusal' = refusal)
    (hLedger : ledger' = ledger)
    (hTransport : transport' = transport)
    (hContinuation : continuation' = continuation)
    (hProvenance : provenance' = provenance)
    (hLocalName : localName' = localName) :
    CertificateTruthBranchBoundaryUp.mk query' assumption' refutation' decision' refusal'
        ledger' transport' continuation' provenance' localName' =
      CertificateTruthBranchBoundaryUp.mk query assumption refutation decision refusal ledger
        transport continuation provenance localName := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hQuery
  cases hAssumption
  cases hRefutation
  cases hDecision
  cases hRefusal
  cases hLedger
  cases hTransport
  cases hContinuation
  cases hProvenance
  cases hLocalName
  rfl

private theorem certificateTruthBranchBoundary_round_trip :
    ∀ x : CertificateTruthBranchBoundaryUp,
      certificateTruthBranchBoundaryFromEventFlow
        (certificateTruthBranchBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk query assumption refutation decision refusal ledger transport continuation provenance
      localName =>
      change
        some
          (CertificateTruthBranchBoundaryUp.mk
            (certificateTruthBranchBoundaryDecodeBHist
              (certificateTruthBranchBoundaryEncodeBHist query))
            (certificateTruthBranchBoundaryDecodeBHist
              (certificateTruthBranchBoundaryEncodeBHist assumption))
            (certificateTruthBranchBoundaryDecodeBHist
              (certificateTruthBranchBoundaryEncodeBHist refutation))
            (certificateTruthBranchBoundaryDecodeBHist
              (certificateTruthBranchBoundaryEncodeBHist decision))
            (certificateTruthBranchBoundaryDecodeBHist
              (certificateTruthBranchBoundaryEncodeBHist refusal))
            (certificateTruthBranchBoundaryDecodeBHist
              (certificateTruthBranchBoundaryEncodeBHist ledger))
            (certificateTruthBranchBoundaryDecodeBHist
              (certificateTruthBranchBoundaryEncodeBHist transport))
            (certificateTruthBranchBoundaryDecodeBHist
              (certificateTruthBranchBoundaryEncodeBHist continuation))
            (certificateTruthBranchBoundaryDecodeBHist
              (certificateTruthBranchBoundaryEncodeBHist provenance))
            (certificateTruthBranchBoundaryDecodeBHist
              (certificateTruthBranchBoundaryEncodeBHist localName))) =
          some
            (CertificateTruthBranchBoundaryUp.mk query assumption refutation decision
              refusal ledger transport continuation provenance localName)
      exact
        congrArg some
          (certificateTruthBranchBoundary_mk_congr
            (certificateTruthBranchBoundaryDecode_encode_bhist query)
            (certificateTruthBranchBoundaryDecode_encode_bhist assumption)
            (certificateTruthBranchBoundaryDecode_encode_bhist refutation)
            (certificateTruthBranchBoundaryDecode_encode_bhist decision)
            (certificateTruthBranchBoundaryDecode_encode_bhist refusal)
            (certificateTruthBranchBoundaryDecode_encode_bhist ledger)
            (certificateTruthBranchBoundaryDecode_encode_bhist transport)
            (certificateTruthBranchBoundaryDecode_encode_bhist continuation)
            (certificateTruthBranchBoundaryDecode_encode_bhist provenance)
            (certificateTruthBranchBoundaryDecode_encode_bhist localName))

private theorem certificateTruthBranchBoundaryToEventFlow_injective
    {x y : CertificateTruthBranchBoundaryUp} :
    certificateTruthBranchBoundaryToEventFlow x =
      certificateTruthBranchBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      certificateTruthBranchBoundaryFromEventFlow
          (certificateTruthBranchBoundaryToEventFlow x) =
        certificateTruthBranchBoundaryFromEventFlow
          (certificateTruthBranchBoundaryToEventFlow y) :=
    congrArg certificateTruthBranchBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (certificateTruthBranchBoundary_round_trip x).symm
      (Eq.trans hread (certificateTruthBranchBoundary_round_trip y)))

instance certificateTruthBranchBoundaryBHistCarrier :
    BHistCarrier CertificateTruthBranchBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := certificateTruthBranchBoundaryToEventFlow
  fromEventFlow := certificateTruthBranchBoundaryFromEventFlow

instance certificateTruthBranchBoundaryChapterTasteGate :
    ChapterTasteGate CertificateTruthBranchBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      certificateTruthBranchBoundaryFromEventFlow
        (certificateTruthBranchBoundaryToEventFlow x) = some x
    exact certificateTruthBranchBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (certificateTruthBranchBoundaryToEventFlow_injective heq)

instance certificateTruthBranchBoundaryFieldFaithful :
    FieldFaithful CertificateTruthBranchBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := certificateTruthBranchBoundaryFields
  field_faithful := by
    intro x y hfields
    cases x with
    | mk query assumption refutation decision refusal ledger transport continuation provenance
        localName =>
        cases y with
        | mk query' assumption' refutation' decision' refusal' ledger' transport'
            continuation' provenance' localName' =>
            cases hfields
            rfl

def taste_gate : ChapterTasteGate CertificateTruthBranchBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  certificateTruthBranchBoundaryChapterTasteGate

end BEDC.Derived.CertificateTruthBranchBoundaryUp
