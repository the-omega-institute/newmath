import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SocketReportUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SocketReportUp : Type where
  | mk :
      (site requestedSupply socketKind auditGate transport continuation provenance
        localName : BHist) →
        SocketReportUp
  deriving DecidableEq

def socketReportEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: socketReportEncodeBHist h
  | BHist.e1 h => BMark.b1 :: socketReportEncodeBHist h

def socketReportDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (socketReportDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (socketReportDecodeBHist tail)

private theorem SocketReportTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, socketReportDecodeBHist (socketReportEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def socketReportFields : SocketReportUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SocketReportUp.mk site requestedSupply socketKind auditGate transport continuation
      provenance localName =>
      [site, requestedSupply, socketKind, auditGate, transport, continuation, provenance,
        localName]

def socketReportToEventFlow : SocketReportUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (socketReportFields x).map socketReportEncodeBHist

def socketReportFromEventFlow : EventFlow → Option SocketReportUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | site :: rest0 =>
      match rest0 with
      | [] => none
      | requestedSupply :: rest1 =>
          match rest1 with
          | [] => none
          | socketKind :: rest2 =>
              match rest2 with
              | [] => none
              | auditGate :: rest3 =>
                  match rest3 with
                  | [] => none
                  | transport :: rest4 =>
                      match rest4 with
                      | [] => none
                      | continuation :: rest5 =>
                          match rest5 with
                          | [] => none
                          | provenance :: rest6 =>
                              match rest6 with
                              | [] => none
                              | localName :: rest7 =>
                                  match rest7 with
                                  | [] =>
                                      some
                                        (SocketReportUp.mk
                                          (socketReportDecodeBHist site)
                                          (socketReportDecodeBHist requestedSupply)
                                          (socketReportDecodeBHist socketKind)
                                          (socketReportDecodeBHist auditGate)
                                          (socketReportDecodeBHist transport)
                                          (socketReportDecodeBHist continuation)
                                          (socketReportDecodeBHist provenance)
                                          (socketReportDecodeBHist localName))
                                  | _ :: _ => none

private theorem SocketReportTasteGate_single_carrier_alignment_round_trip :
    ∀ x : SocketReportUp, socketReportFromEventFlow (socketReportToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk site requestedSupply socketKind auditGate transport continuation provenance localName =>
      change
        some
          (SocketReportUp.mk
            (socketReportDecodeBHist (socketReportEncodeBHist site))
            (socketReportDecodeBHist (socketReportEncodeBHist requestedSupply))
            (socketReportDecodeBHist (socketReportEncodeBHist socketKind))
            (socketReportDecodeBHist (socketReportEncodeBHist auditGate))
            (socketReportDecodeBHist (socketReportEncodeBHist transport))
            (socketReportDecodeBHist (socketReportEncodeBHist continuation))
            (socketReportDecodeBHist (socketReportEncodeBHist provenance))
            (socketReportDecodeBHist (socketReportEncodeBHist localName))) =
          some
            (SocketReportUp.mk site requestedSupply socketKind auditGate transport continuation
              provenance localName)
      rw [SocketReportTasteGate_single_carrier_alignment_decode_encode site,
        SocketReportTasteGate_single_carrier_alignment_decode_encode requestedSupply,
        SocketReportTasteGate_single_carrier_alignment_decode_encode socketKind,
        SocketReportTasteGate_single_carrier_alignment_decode_encode auditGate,
        SocketReportTasteGate_single_carrier_alignment_decode_encode transport,
        SocketReportTasteGate_single_carrier_alignment_decode_encode continuation,
        SocketReportTasteGate_single_carrier_alignment_decode_encode provenance,
        SocketReportTasteGate_single_carrier_alignment_decode_encode localName]

private theorem SocketReportTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SocketReportUp} :
    socketReportToEventFlow x = socketReportToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      socketReportFromEventFlow (socketReportToEventFlow x) =
        socketReportFromEventFlow (socketReportToEventFlow y) :=
    congrArg socketReportFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (SocketReportTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (SocketReportTasteGate_single_carrier_alignment_round_trip y)))

private theorem SocketReportTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : SocketReportUp, socketReportFields x = socketReportFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk site₁ requestedSupply₁ socketKind₁ auditGate₁ transport₁ continuation₁
      provenance₁ localName₁ =>
      cases y with
      | mk site₂ requestedSupply₂ socketKind₂ auditGate₂ transport₂ continuation₂
          provenance₂ localName₂ =>
          injection hfields with hSite tail0
          injection tail0 with hRequestedSupply tail1
          injection tail1 with hSocketKind tail2
          injection tail2 with hAuditGate tail3
          injection tail3 with hTransport tail4
          injection tail4 with hContinuation tail5
          injection tail5 with hProvenance tail6
          injection tail6 with hLocalName _
          subst hSite
          subst hRequestedSupply
          subst hSocketKind
          subst hAuditGate
          subst hTransport
          subst hContinuation
          subst hProvenance
          subst hLocalName
          rfl

instance socketReportBHistCarrier : BHistCarrier SocketReportUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := socketReportToEventFlow
  fromEventFlow := socketReportFromEventFlow

instance socketReportChapterTasteGate : ChapterTasteGate SocketReportUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change socketReportFromEventFlow (socketReportToEventFlow x) = some x
    exact SocketReportTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SocketReportTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance socketReportFieldFaithful : FieldFaithful SocketReportUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := socketReportFields
  field_faithful := SocketReportTasteGate_single_carrier_alignment_fields_faithful

instance socketReportNontrivial : Nontrivial SocketReportUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SocketReportUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      SocketReportUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate SocketReportUp :=
  -- BEDC touchpoint anchor: BHist BMark
  socketReportChapterTasteGate

theorem SocketReportTasteGate_single_carrier_alignment :
    (∀ h : BHist, socketReportDecodeBHist (socketReportEncodeBHist h) = h) ∧
      (∀ x : SocketReportUp, socketReportFromEventFlow (socketReportToEventFlow x) = some x) ∧
        (∀ x y : SocketReportUp, socketReportToEventFlow x = socketReportToEventFlow y → x = y) ∧
          socketReportEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨SocketReportTasteGate_single_carrier_alignment_decode_encode,
      SocketReportTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => SocketReportTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.SocketReportUp
