import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NegativeCertificateBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NegativeCertificateBoundaryUp : Type where
  | mk :
      (socket internalizer gapLedger auditReadback transport continuation provenance name :
        BHist) →
      NegativeCertificateBoundaryUp
  deriving DecidableEq

def negativeCertificateBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: negativeCertificateBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: negativeCertificateBoundaryEncodeBHist h

def negativeCertificateBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (negativeCertificateBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (negativeCertificateBoundaryDecodeBHist tail)

private theorem negativeCertificateBoundaryDecode_encode_bhist :
    ∀ h : BHist,
      negativeCertificateBoundaryDecodeBHist (negativeCertificateBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem negativeCertificateBoundary_mk_congr
    {socket socket' internalizer internalizer' gapLedger gapLedger'
      auditReadback auditReadback' transport transport' continuation continuation'
      provenance provenance' name name' : BHist}
    (hSocket : socket' = socket)
    (hInternalizer : internalizer' = internalizer)
    (hGapLedger : gapLedger' = gapLedger)
    (hAuditReadback : auditReadback' = auditReadback)
    (hTransport : transport' = transport)
    (hContinuation : continuation' = continuation)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    NegativeCertificateBoundaryUp.mk socket' internalizer' gapLedger' auditReadback'
        transport' continuation' provenance' name' =
      NegativeCertificateBoundaryUp.mk socket internalizer gapLedger auditReadback transport
        continuation provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hSocket
  cases hInternalizer
  cases hGapLedger
  cases hAuditReadback
  cases hTransport
  cases hContinuation
  cases hProvenance
  cases hName
  rfl

def negativeCertificateBoundaryToEventFlow :
    NegativeCertificateBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | NegativeCertificateBoundaryUp.mk socket internalizer gapLedger auditReadback transport
      continuation provenance name =>
      [[BMark.b0],
        negativeCertificateBoundaryEncodeBHist socket,
        [BMark.b1, BMark.b0],
        negativeCertificateBoundaryEncodeBHist internalizer,
        [BMark.b1, BMark.b1, BMark.b0],
        negativeCertificateBoundaryEncodeBHist gapLedger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        negativeCertificateBoundaryEncodeBHist auditReadback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        negativeCertificateBoundaryEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        negativeCertificateBoundaryEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        negativeCertificateBoundaryEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        negativeCertificateBoundaryEncodeBHist name]

def negativeCertificateBoundaryFromEventFlow :
    EventFlow → Option NegativeCertificateBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | socket :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | internalizer :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | gapLedger :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | auditReadback :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | transport :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | continuation :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | provenance :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | name :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (NegativeCertificateBoundaryUp.mk
                                                                          (negativeCertificateBoundaryDecodeBHist socket)
                                                                          (negativeCertificateBoundaryDecodeBHist internalizer)
                                                                          (negativeCertificateBoundaryDecodeBHist gapLedger)
                                                                          (negativeCertificateBoundaryDecodeBHist auditReadback)
                                                                          (negativeCertificateBoundaryDecodeBHist transport)
                                                                          (negativeCertificateBoundaryDecodeBHist continuation)
                                                                          (negativeCertificateBoundaryDecodeBHist provenance)
                                                                          (negativeCertificateBoundaryDecodeBHist name))
                                                                  | _ :: _ => none

private theorem negativeCertificateBoundary_round_trip :
    ∀ x : NegativeCertificateBoundaryUp,
      negativeCertificateBoundaryFromEventFlow
        (negativeCertificateBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk socket internalizer gapLedger auditReadback transport continuation provenance name =>
      change
        some
          (NegativeCertificateBoundaryUp.mk
            (negativeCertificateBoundaryDecodeBHist
              (negativeCertificateBoundaryEncodeBHist socket))
            (negativeCertificateBoundaryDecodeBHist
              (negativeCertificateBoundaryEncodeBHist internalizer))
            (negativeCertificateBoundaryDecodeBHist
              (negativeCertificateBoundaryEncodeBHist gapLedger))
            (negativeCertificateBoundaryDecodeBHist
              (negativeCertificateBoundaryEncodeBHist auditReadback))
            (negativeCertificateBoundaryDecodeBHist
              (negativeCertificateBoundaryEncodeBHist transport))
            (negativeCertificateBoundaryDecodeBHist
              (negativeCertificateBoundaryEncodeBHist continuation))
            (negativeCertificateBoundaryDecodeBHist
              (negativeCertificateBoundaryEncodeBHist provenance))
            (negativeCertificateBoundaryDecodeBHist
              (negativeCertificateBoundaryEncodeBHist name))) =
          some
            (NegativeCertificateBoundaryUp.mk socket internalizer gapLedger auditReadback
              transport continuation provenance name)
      exact
        congrArg some
          (negativeCertificateBoundary_mk_congr
            (negativeCertificateBoundaryDecode_encode_bhist socket)
            (negativeCertificateBoundaryDecode_encode_bhist internalizer)
            (negativeCertificateBoundaryDecode_encode_bhist gapLedger)
            (negativeCertificateBoundaryDecode_encode_bhist auditReadback)
            (negativeCertificateBoundaryDecode_encode_bhist transport)
            (negativeCertificateBoundaryDecode_encode_bhist continuation)
            (negativeCertificateBoundaryDecode_encode_bhist provenance)
            (negativeCertificateBoundaryDecode_encode_bhist name))

private theorem negativeCertificateBoundary_event_flow_injective
    {x y : NegativeCertificateBoundaryUp} :
    negativeCertificateBoundaryToEventFlow x =
      negativeCertificateBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      negativeCertificateBoundaryFromEventFlow
          (negativeCertificateBoundaryToEventFlow x) =
        negativeCertificateBoundaryFromEventFlow
          (negativeCertificateBoundaryToEventFlow y) :=
    congrArg negativeCertificateBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (negativeCertificateBoundary_round_trip x).symm
      (Eq.trans hread (negativeCertificateBoundary_round_trip y)))

instance negativeCertificateBoundaryBHistCarrier :
    BHistCarrier NegativeCertificateBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := negativeCertificateBoundaryToEventFlow
  fromEventFlow := negativeCertificateBoundaryFromEventFlow

instance negativeCertificateBoundaryChapterTasteGate :
    ChapterTasteGate NegativeCertificateBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      negativeCertificateBoundaryFromEventFlow
        (negativeCertificateBoundaryToEventFlow x) = some x
    exact negativeCertificateBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (negativeCertificateBoundary_event_flow_injective heq)

def negativeCertificateBoundaryFields : NegativeCertificateBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | NegativeCertificateBoundaryUp.mk socket internalizer gapLedger auditReadback transport
      continuation provenance name =>
      [socket, internalizer, gapLedger, auditReadback, transport, continuation, provenance,
        name]

private theorem negativeCertificateBoundary_field_faithful_concrete :
    ∀ x y : NegativeCertificateBoundaryUp,
      negativeCertificateBoundaryFields x = negativeCertificateBoundaryFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk socket internalizer gapLedger auditReadback transport continuation provenance name =>
      cases y with
      | mk socket' internalizer' gapLedger' auditReadback' transport' continuation'
          provenance' name' =>
          injection hfields with hSocket tail0
          injection tail0 with hInternalizer tail1
          injection tail1 with hGapLedger tail2
          injection tail2 with hAuditReadback tail3
          injection tail3 with hTransport tail4
          injection tail4 with hContinuation tail5
          injection tail5 with hProvenance tail6
          injection tail6 with hName _hNil
          cases hSocket
          cases hInternalizer
          cases hGapLedger
          cases hAuditReadback
          cases hTransport
          cases hContinuation
          cases hProvenance
          cases hName
          rfl

instance negativeCertificateBoundaryFieldFaithful :
    FieldFaithful NegativeCertificateBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := negativeCertificateBoundaryFields
  field_faithful := negativeCertificateBoundary_field_faithful_concrete

private def negativeCertificateBoundary_nontrivial_witness :
    Σ' (x : NegativeCertificateBoundaryUp) (y : NegativeCertificateBoundaryUp), x ≠ y :=
  ⟨NegativeCertificateBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
      BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
    NegativeCertificateBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
      BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
    by
      -- BEDC touchpoint anchor: BHist BMark
      intro h
      cases h⟩

instance negativeCertificateBoundaryNontrivial :
    Nontrivial NegativeCertificateBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair := negativeCertificateBoundary_nontrivial_witness

theorem NegativeCertificateBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      negativeCertificateBoundaryDecodeBHist
        (negativeCertificateBoundaryEncodeBHist h) = h) ∧
      (∀ x : NegativeCertificateBoundaryUp,
        negativeCertificateBoundaryFromEventFlow
          (negativeCertificateBoundaryToEventFlow x) = some x) ∧
        (∀ x y : NegativeCertificateBoundaryUp,
          negativeCertificateBoundaryToEventFlow x =
            negativeCertificateBoundaryToEventFlow y → x = y) ∧
          negativeCertificateBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact negativeCertificateBoundaryDecode_encode_bhist
  · constructor
    · exact negativeCertificateBoundary_round_trip
    · constructor
      · intro x y heq
        exact negativeCertificateBoundary_event_flow_injective heq
      · rfl

def NegativeCertificateBoundaryCarrier [AskSetup] [PackageSetup]
    (socket internalizer gapLedger auditReadback transport continuation provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory socket ∧ UnaryHistory internalizer ∧ UnaryHistory gapLedger ∧
    UnaryHistory auditReadback ∧ UnaryHistory transport ∧ UnaryHistory continuation ∧
      UnaryHistory provenance ∧ UnaryHistory name ∧ Cont socket internalizer gapLedger ∧
        Cont gapLedger auditReadback continuation ∧ PkgSig bundle auditReadback pkg ∧
          hsame name provenance

theorem NegativeCertificateBoundaryCarrier_audit_surface [AskSetup] [PackageSetup]
    {socket internalizer gapLedger auditReadback transport continuation provenance name
      consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NegativeCertificateBoundaryCarrier socket internalizer gapLedger auditReadback transport
        continuation provenance name bundle pkg →
      Cont auditReadback continuation consumer →
        PkgSig bundle consumer pkg →
          SemanticNameCert
            (fun row : BHist =>
              NegativeCertificateBoundaryCarrier socket internalizer gapLedger auditReadback
                  transport continuation provenance name bundle pkg ∧
                hsame row consumer)
            (fun row : BHist =>
              Cont socket internalizer gapLedger ∧ Cont gapLedger auditReadback continuation ∧
                Cont auditReadback continuation row)
            (fun row : BHist =>
              UnaryHistory row ∧ PkgSig bundle consumer pkg ∧ hsame name provenance)
            hsame := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig SemanticNameCert hsame
  intro carrier auditConsumer consumerPkg
  have carrierWitness := carrier
  obtain ⟨_socketUnary, _internalizerUnary, _gapLedgerUnary, auditReadbackUnary, _transportUnary,
    continuationUnary, _provenanceUnary, _nameUnary, socketInternalizerGap,
    gapAuditContinuation, _auditPkg, nameProvenance⟩ := carrier
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed auditReadbackUnary continuationUnary auditConsumer
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro consumer (And.intro carrierWitness (hsame_refl consumer))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro row source
      exact
        ⟨socketInternalizerGap, gapAuditContinuation,
          cont_result_hsame_transport auditConsumer (hsame_symm source.right)⟩
    ledger_sound := by
      intro row source
      exact
        ⟨unary_transport consumerUnary (hsame_symm source.right), consumerPkg,
          nameProvenance⟩
  }

end BEDC.Derived.NegativeCertificateBoundaryUp
