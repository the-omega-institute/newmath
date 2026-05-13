import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.KernelAcceptanceTraceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def KernelAcceptanceTraceCarrier [AskSetup] [PackageSetup]
    (candidate ty classifier stamp env ledger transport route provenance cert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory candidate ∧ UnaryHistory ty ∧ UnaryHistory classifier ∧
    UnaryHistory stamp ∧ UnaryHistory env ∧ UnaryHistory ledger ∧
      UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
        UnaryHistory cert ∧ Cont candidate ty classifier ∧ Cont classifier stamp env ∧
          Cont env ledger route ∧ hsame endpointLedger transport ∧
            hsame endpointLedger ledger ∧ PkgSig bundle endpointLedger pkg
where
  endpointLedger : BHist := append route cert

theorem KernelAcceptanceTraceCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {candidate ty classifier stamp env ledger transport route provenance cert endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KernelAcceptanceTraceCarrier candidate ty classifier stamp env ledger transport route
        provenance cert bundle pkg →
      Cont route cert endpoint →
        PkgSig bundle endpoint pkg →
          SemanticNameCert
              (fun row : BHist =>
                KernelAcceptanceTraceCarrier candidate ty classifier stamp env ledger transport
                  route provenance cert bundle pkg ∧ hsame row endpoint)
              (fun row : BHist => hsame row ledger)
              (fun row : BHist => hsame row ledger ∧ PkgSig bundle endpoint pkg)
              hsame ∧
            UnaryHistory candidate ∧ UnaryHistory ty ∧ UnaryHistory classifier ∧
              UnaryHistory stamp ∧ UnaryHistory env ∧ UnaryHistory ledger ∧
                UnaryHistory endpoint ∧ Cont candidate ty classifier ∧
                  Cont classifier stamp env ∧ Cont env ledger route ∧
                    Cont route cert endpoint := by
  -- BEDC touchpoint anchor: BHist KernelAcceptanceTraceCarrier hsame SemanticNameCert
  intro carrierData endpointRoute packageRow
  have carrier := carrierData
  obtain ⟨candidateUnary, tyUnary, classifierUnary, stampUnary, envUnary, ledgerUnary,
    _transportUnary, routeUnary, _provenanceUnary, certUnary, candidateTyClassifier,
    classifierStampEnv, envLedgerRoute, _transportSame, endpointLedgerSame, _endpointPackage⟩ :=
      carrierData
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed routeUnary certUnary endpointRoute
  have endpointSameLedger : hsame endpoint ledger := by
    cases endpointRoute
    exact endpointLedgerSame
  have certSurface :
      SemanticNameCert
          (fun row : BHist =>
            KernelAcceptanceTraceCarrier candidate ty classifier stamp env ledger transport route
              provenance cert bundle pkg ∧ hsame row endpoint)
          (fun row : BHist => hsame row ledger)
          (fun row : BHist => hsame row ledger ∧ PkgSig bundle endpoint pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint (And.intro carrier (hsame_refl endpoint))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows sourceRow
        exact And.intro sourceRow.left (hsame_trans (hsame_symm sameRows) sourceRow.right)
    }
    pattern_sound := by
      intro _row sourceRow
      exact hsame_trans sourceRow.right endpointSameLedger
    ledger_sound := by
      intro _row sourceRow
      exact And.intro (hsame_trans sourceRow.right endpointSameLedger) packageRow
  }
  exact
    And.intro certSurface
      (And.intro candidateUnary
        (And.intro tyUnary
          (And.intro classifierUnary
            (And.intro stampUnary
              (And.intro envUnary
                (And.intro ledgerUnary
                  (And.intro endpointUnary
                    (And.intro candidateTyClassifier
                      (And.intro classifierStampEnv
                        (And.intro envLedgerRoute endpointRoute))))))))))

inductive KernelAcceptanceTraceUp : Type where
  | mk :
      (candidate typeRow classifier stamp environment axiomLedger transport route provenance
        localName : BHist) →
      KernelAcceptanceTraceUp
  deriving DecidableEq

private def kernelAcceptanceTraceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: kernelAcceptanceTraceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: kernelAcceptanceTraceEncodeBHist h

private def kernelAcceptanceTraceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (kernelAcceptanceTraceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (kernelAcceptanceTraceDecodeBHist tail)

private theorem kernelAcceptanceTraceDecode_encode_bhist :
    ∀ h : BHist, kernelAcceptanceTraceDecodeBHist (kernelAcceptanceTraceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem kernelAcceptanceTrace_mk_congr
    {candidate candidate' typeRow typeRow' classifier classifier' stamp stamp'
      environment environment' axiomLedger axiomLedger' transport transport' route route'
      provenance provenance' localName localName' : BHist}
    (hCandidate : candidate' = candidate)
    (hTypeRow : typeRow' = typeRow)
    (hClassifier : classifier' = classifier)
    (hStamp : stamp' = stamp)
    (hEnvironment : environment' = environment)
    (hAxiomLedger : axiomLedger' = axiomLedger)
    (hTransport : transport' = transport)
    (hRoute : route' = route)
    (hProvenance : provenance' = provenance)
    (hLocalName : localName' = localName) :
    KernelAcceptanceTraceUp.mk candidate' typeRow' classifier' stamp' environment'
        axiomLedger' transport' route' provenance' localName' =
      KernelAcceptanceTraceUp.mk candidate typeRow classifier stamp environment axiomLedger
        transport route provenance localName := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hCandidate
  cases hTypeRow
  cases hClassifier
  cases hStamp
  cases hEnvironment
  cases hAxiomLedger
  cases hTransport
  cases hRoute
  cases hProvenance
  cases hLocalName
  rfl

private def kernelAcceptanceTraceToEventFlow : KernelAcceptanceTraceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | KernelAcceptanceTraceUp.mk candidate typeRow classifier stamp environment axiomLedger
      transport route provenance localName =>
      [[BMark.b0],
        kernelAcceptanceTraceEncodeBHist candidate,
        [BMark.b1, BMark.b0],
        kernelAcceptanceTraceEncodeBHist typeRow,
        [BMark.b1, BMark.b1, BMark.b0],
        kernelAcceptanceTraceEncodeBHist classifier,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        kernelAcceptanceTraceEncodeBHist stamp,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        kernelAcceptanceTraceEncodeBHist environment,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        kernelAcceptanceTraceEncodeBHist axiomLedger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        kernelAcceptanceTraceEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        kernelAcceptanceTraceEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        kernelAcceptanceTraceEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        kernelAcceptanceTraceEncodeBHist localName]

private def kernelAcceptanceTraceFromEventFlow : EventFlow → Option KernelAcceptanceTraceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | candidate :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | typeRow :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | classifier :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | stamp :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | environment :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | axiomLedger :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | transport :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | route :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | provenance :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | localName :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      some
                                                                                        (KernelAcceptanceTraceUp.mk
                                                                                          (kernelAcceptanceTraceDecodeBHist candidate)
                                                                                          (kernelAcceptanceTraceDecodeBHist typeRow)
                                                                                          (kernelAcceptanceTraceDecodeBHist classifier)
                                                                                          (kernelAcceptanceTraceDecodeBHist stamp)
                                                                                          (kernelAcceptanceTraceDecodeBHist environment)
                                                                                          (kernelAcceptanceTraceDecodeBHist axiomLedger)
                                                                                          (kernelAcceptanceTraceDecodeBHist transport)
                                                                                          (kernelAcceptanceTraceDecodeBHist route)
                                                                                          (kernelAcceptanceTraceDecodeBHist provenance)
                                                                                          (kernelAcceptanceTraceDecodeBHist localName))
                                                                                  | _ :: _ => none

private theorem kernelAcceptanceTrace_round_trip :
    ∀ x : KernelAcceptanceTraceUp,
      kernelAcceptanceTraceFromEventFlow (kernelAcceptanceTraceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk candidate typeRow classifier stamp environment axiomLedger transport route provenance
      localName =>
      change
        some
          (KernelAcceptanceTraceUp.mk
            (kernelAcceptanceTraceDecodeBHist (kernelAcceptanceTraceEncodeBHist candidate))
            (kernelAcceptanceTraceDecodeBHist (kernelAcceptanceTraceEncodeBHist typeRow))
            (kernelAcceptanceTraceDecodeBHist (kernelAcceptanceTraceEncodeBHist classifier))
            (kernelAcceptanceTraceDecodeBHist (kernelAcceptanceTraceEncodeBHist stamp))
            (kernelAcceptanceTraceDecodeBHist (kernelAcceptanceTraceEncodeBHist environment))
            (kernelAcceptanceTraceDecodeBHist (kernelAcceptanceTraceEncodeBHist axiomLedger))
            (kernelAcceptanceTraceDecodeBHist (kernelAcceptanceTraceEncodeBHist transport))
            (kernelAcceptanceTraceDecodeBHist (kernelAcceptanceTraceEncodeBHist route))
            (kernelAcceptanceTraceDecodeBHist (kernelAcceptanceTraceEncodeBHist provenance))
            (kernelAcceptanceTraceDecodeBHist (kernelAcceptanceTraceEncodeBHist localName))) =
          some
            (KernelAcceptanceTraceUp.mk candidate typeRow classifier stamp environment
              axiomLedger transport route provenance localName)
      exact
        congrArg some
          (kernelAcceptanceTrace_mk_congr
            (kernelAcceptanceTraceDecode_encode_bhist candidate)
            (kernelAcceptanceTraceDecode_encode_bhist typeRow)
            (kernelAcceptanceTraceDecode_encode_bhist classifier)
            (kernelAcceptanceTraceDecode_encode_bhist stamp)
            (kernelAcceptanceTraceDecode_encode_bhist environment)
            (kernelAcceptanceTraceDecode_encode_bhist axiomLedger)
            (kernelAcceptanceTraceDecode_encode_bhist transport)
            (kernelAcceptanceTraceDecode_encode_bhist route)
            (kernelAcceptanceTraceDecode_encode_bhist provenance)
            (kernelAcceptanceTraceDecode_encode_bhist localName))

private theorem kernelAcceptanceTraceToEventFlow_injective {x y : KernelAcceptanceTraceUp} :
    kernelAcceptanceTraceToEventFlow x = kernelAcceptanceTraceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      kernelAcceptanceTraceFromEventFlow (kernelAcceptanceTraceToEventFlow x) =
        kernelAcceptanceTraceFromEventFlow (kernelAcceptanceTraceToEventFlow y) :=
    congrArg kernelAcceptanceTraceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (kernelAcceptanceTrace_round_trip x).symm
      (Eq.trans hread (kernelAcceptanceTrace_round_trip y)))

instance kernelAcceptanceTraceBHistCarrier : BHistCarrier KernelAcceptanceTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := kernelAcceptanceTraceToEventFlow
  fromEventFlow := kernelAcceptanceTraceFromEventFlow

instance kernelAcceptanceTraceChapterTasteGate : ChapterTasteGate KernelAcceptanceTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change kernelAcceptanceTraceFromEventFlow (kernelAcceptanceTraceToEventFlow x) = some x
    exact kernelAcceptanceTrace_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (kernelAcceptanceTraceToEventFlow_injective heq)

theorem KernelAcceptanceTraceTasteGate_single_carrier_alignment :
    (∀ h : BHist, kernelAcceptanceTraceDecodeBHist (kernelAcceptanceTraceEncodeBHist h) = h) ∧
      (∀ x : KernelAcceptanceTraceUp,
        kernelAcceptanceTraceFromEventFlow (kernelAcceptanceTraceToEventFlow x) = some x) ∧
        (∀ x y : KernelAcceptanceTraceUp,
          kernelAcceptanceTraceToEventFlow x = kernelAcceptanceTraceToEventFlow y → x = y) ∧
          kernelAcceptanceTraceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact kernelAcceptanceTraceDecode_encode_bhist
  · constructor
    · exact kernelAcceptanceTrace_round_trip
    · constructor
      · intro x y heq
        exact kernelAcceptanceTraceToEventFlow_injective heq
      · rfl

end BEDC.Derived.KernelAcceptanceTraceUp
