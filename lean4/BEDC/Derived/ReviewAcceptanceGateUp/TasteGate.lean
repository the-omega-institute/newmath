import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ReviewAcceptanceGateUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ReviewAcceptanceGateUp : Type where
  | mk :
      (proposal decision rejected acceptance machineBoundary kernelRows blockedClaims
        transport continuation provenance localName : BHist) →
      ReviewAcceptanceGateUp
  deriving DecidableEq

def reviewAcceptanceGateEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: reviewAcceptanceGateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: reviewAcceptanceGateEncodeBHist h

def reviewAcceptanceGateDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (reviewAcceptanceGateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (reviewAcceptanceGateDecodeBHist tail)

private theorem reviewAcceptanceGate_decode_encode_bhist :
    ∀ h : BHist, reviewAcceptanceGateDecodeBHist (reviewAcceptanceGateEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def reviewAcceptanceGateFields : ReviewAcceptanceGateUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ReviewAcceptanceGateUp.mk proposal decision rejected acceptance machineBoundary
      kernelRows blockedClaims transport continuation provenance localName =>
      [proposal, decision, rejected, acceptance, machineBoundary, kernelRows,
        blockedClaims, transport, continuation, provenance, localName]

def reviewAcceptanceGateToEventFlow : ReviewAcceptanceGateUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (reviewAcceptanceGateFields x).map reviewAcceptanceGateEncodeBHist

def reviewAcceptanceGateFromEventFlow : EventFlow → Option ReviewAcceptanceGateUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | proposal :: rest0 =>
      match rest0 with
      | [] => none
      | decision :: rest1 =>
          match rest1 with
          | [] => none
          | rejected :: rest2 =>
              match rest2 with
              | [] => none
              | acceptance :: rest3 =>
                  match rest3 with
                  | [] => none
                  | machineBoundary :: rest4 =>
                      match rest4 with
                      | [] => none
                      | kernelRows :: rest5 =>
                          match rest5 with
                          | [] => none
                          | blockedClaims :: rest6 =>
                              match rest6 with
                              | [] => none
                              | transport :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | continuation :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | provenance :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | localName :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (ReviewAcceptanceGateUp.mk
                                                      (reviewAcceptanceGateDecodeBHist proposal)
                                                      (reviewAcceptanceGateDecodeBHist decision)
                                                      (reviewAcceptanceGateDecodeBHist rejected)
                                                      (reviewAcceptanceGateDecodeBHist acceptance)
                                                      (reviewAcceptanceGateDecodeBHist
                                                        machineBoundary)
                                                      (reviewAcceptanceGateDecodeBHist kernelRows)
                                                      (reviewAcceptanceGateDecodeBHist
                                                        blockedClaims)
                                                      (reviewAcceptanceGateDecodeBHist transport)
                                                      (reviewAcceptanceGateDecodeBHist continuation)
                                                      (reviewAcceptanceGateDecodeBHist provenance)
                                                      (reviewAcceptanceGateDecodeBHist localName))
                                              | _ :: _ => none

private theorem reviewAcceptanceGate_round_trip :
    ∀ x : ReviewAcceptanceGateUp,
      reviewAcceptanceGateFromEventFlow (reviewAcceptanceGateToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk proposal decision rejected acceptance machineBoundary kernelRows blockedClaims
      transport continuation provenance localName =>
      change
        some
          (ReviewAcceptanceGateUp.mk
            (reviewAcceptanceGateDecodeBHist (reviewAcceptanceGateEncodeBHist proposal))
            (reviewAcceptanceGateDecodeBHist (reviewAcceptanceGateEncodeBHist decision))
            (reviewAcceptanceGateDecodeBHist (reviewAcceptanceGateEncodeBHist rejected))
            (reviewAcceptanceGateDecodeBHist (reviewAcceptanceGateEncodeBHist acceptance))
            (reviewAcceptanceGateDecodeBHist
              (reviewAcceptanceGateEncodeBHist machineBoundary))
            (reviewAcceptanceGateDecodeBHist (reviewAcceptanceGateEncodeBHist kernelRows))
            (reviewAcceptanceGateDecodeBHist
              (reviewAcceptanceGateEncodeBHist blockedClaims))
            (reviewAcceptanceGateDecodeBHist (reviewAcceptanceGateEncodeBHist transport))
            (reviewAcceptanceGateDecodeBHist
              (reviewAcceptanceGateEncodeBHist continuation))
            (reviewAcceptanceGateDecodeBHist (reviewAcceptanceGateEncodeBHist provenance))
            (reviewAcceptanceGateDecodeBHist (reviewAcceptanceGateEncodeBHist localName))) =
          some
            (ReviewAcceptanceGateUp.mk proposal decision rejected acceptance machineBoundary
              kernelRows blockedClaims transport continuation provenance localName)
      rw [reviewAcceptanceGate_decode_encode_bhist proposal,
        reviewAcceptanceGate_decode_encode_bhist decision,
        reviewAcceptanceGate_decode_encode_bhist rejected,
        reviewAcceptanceGate_decode_encode_bhist acceptance,
        reviewAcceptanceGate_decode_encode_bhist machineBoundary,
        reviewAcceptanceGate_decode_encode_bhist kernelRows,
        reviewAcceptanceGate_decode_encode_bhist blockedClaims,
        reviewAcceptanceGate_decode_encode_bhist transport,
        reviewAcceptanceGate_decode_encode_bhist continuation,
        reviewAcceptanceGate_decode_encode_bhist provenance,
        reviewAcceptanceGate_decode_encode_bhist localName]

private theorem reviewAcceptanceGateToEventFlow_injective {x y : ReviewAcceptanceGateUp} :
    reviewAcceptanceGateToEventFlow x = reviewAcceptanceGateToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      reviewAcceptanceGateFromEventFlow (reviewAcceptanceGateToEventFlow x) =
        reviewAcceptanceGateFromEventFlow (reviewAcceptanceGateToEventFlow y) :=
    congrArg reviewAcceptanceGateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (reviewAcceptanceGate_round_trip x).symm
      (Eq.trans hread (reviewAcceptanceGate_round_trip y)))

private theorem reviewAcceptanceGate_field_faithful :
    ∀ x y : ReviewAcceptanceGateUp,
      reviewAcceptanceGateFields x = reviewAcceptanceGateFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk proposalA decisionA rejectedA acceptanceA machineBoundaryA kernelRowsA
      blockedClaimsA transportA continuationA provenanceA localNameA =>
      cases y with
      | mk proposalB decisionB rejectedB acceptanceB machineBoundaryB kernelRowsB
          blockedClaimsB transportB continuationB provenanceB localNameB =>
          injection hfields with hProposal t1
          injection t1 with hDecision t2
          injection t2 with hRejected t3
          injection t3 with hAcceptance t4
          injection t4 with hMachineBoundary t5
          injection t5 with hKernelRows t6
          injection t6 with hBlockedClaims t7
          injection t7 with hTransport t8
          injection t8 with hContinuation t9
          injection t9 with hProvenance t10
          injection t10 with hLocalName _
          cases hProposal
          cases hDecision
          cases hRejected
          cases hAcceptance
          cases hMachineBoundary
          cases hKernelRows
          cases hBlockedClaims
          cases hTransport
          cases hContinuation
          cases hProvenance
          cases hLocalName
          rfl

instance reviewAcceptanceGateBHistCarrier : BHistCarrier ReviewAcceptanceGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := reviewAcceptanceGateToEventFlow
  fromEventFlow := reviewAcceptanceGateFromEventFlow

instance reviewAcceptanceGateChapterTasteGate : ChapterTasteGate ReviewAcceptanceGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change reviewAcceptanceGateFromEventFlow (reviewAcceptanceGateToEventFlow x) = some x
    exact reviewAcceptanceGate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (reviewAcceptanceGateToEventFlow_injective heq)

instance reviewAcceptanceGateFieldFaithful : FieldFaithful ReviewAcceptanceGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := reviewAcceptanceGateFields
  field_faithful := reviewAcceptanceGate_field_faithful

instance reviewAcceptanceGateNontrivial : Nontrivial ReviewAcceptanceGateUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ReviewAcceptanceGateUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      ReviewAcceptanceGateUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem ReviewAcceptanceGateTasteGate_single_carrier_alignment :
    (∀ h : BHist, reviewAcceptanceGateDecodeBHist (reviewAcceptanceGateEncodeBHist h) = h) ∧
      (∀ x : ReviewAcceptanceGateUp,
        reviewAcceptanceGateFromEventFlow (reviewAcceptanceGateToEventFlow x) = some x) ∧
        (∀ x y : ReviewAcceptanceGateUp,
          reviewAcceptanceGateToEventFlow x = reviewAcceptanceGateToEventFlow y → x = y) ∧
          reviewAcceptanceGateEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨reviewAcceptanceGate_decode_encode_bhist, reviewAcceptanceGate_round_trip,
      (fun _ _ heq => reviewAcceptanceGateToEventFlow_injective heq), rfl⟩

end BEDC.Derived.ReviewAcceptanceGateUp
