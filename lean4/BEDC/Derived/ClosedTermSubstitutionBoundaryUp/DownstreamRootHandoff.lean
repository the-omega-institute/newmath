import BEDC.Derived.ClosedTermSubstitutionBoundaryUp
import BEDC.FKernel.Sig

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryDownstreamRootHandoff [AskSetup] [PackageSetup]
    {source value depth shift substitution ledger audit route binder compiler recursor authorized
      normalization handoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont shift substitution ledger ->
        Cont substitution depth audit ->
          Cont ledger audit route ->
            Cont route ledger binder ->
              Cont route audit compiler ->
                Cont binder compiler recursor ->
                  Cont recursor audit authorized ->
                    Cont authorized route normalization ->
                      Cont normalization audit handoff ->
                        PkgSig bundle handoff pkg ->
                          UnaryHistory binder ∧ UnaryHistory compiler ∧ UnaryHistory recursor ∧
                            UnaryHistory authorized ∧ UnaryHistory normalization ∧
                              UnaryHistory handoff ∧ Cont normalization audit handoff ∧
                                PkgSig bundle handoff pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro classifier shiftSubstitutionLedger substitutionDepthAudit ledgerAuditRoute
    routeLedgerBinder routeAuditCompiler binderCompilerRecursor recursorAuditAuthorized
    authorizedRouteNormalization normalizationAuditHandoff handoffPkg
  obtain ⟨_sourceUnary, _valueUnary, depthUnary, shiftUnary, substitutionUnary,
    _sourceValueShift, _shiftDepthSubstitution⟩ := classifier
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed shiftUnary substitutionUnary shiftSubstitutionLedger
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed substitutionUnary depthUnary substitutionDepthAudit
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary auditUnary ledgerAuditRoute
  have binderUnary : UnaryHistory binder :=
    unary_cont_closed routeUnary ledgerUnary routeLedgerBinder
  have compilerUnary : UnaryHistory compiler :=
    unary_cont_closed routeUnary auditUnary routeAuditCompiler
  have recursorUnary : UnaryHistory recursor :=
    unary_cont_closed binderUnary compilerUnary binderCompilerRecursor
  have authorizedUnary : UnaryHistory authorized :=
    unary_cont_closed recursorUnary auditUnary recursorAuditAuthorized
  have normalizationUnary : UnaryHistory normalization :=
    unary_cont_closed authorizedUnary routeUnary authorizedRouteNormalization
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed normalizationUnary auditUnary normalizationAuditHandoff
  exact
    ⟨binderUnary, compilerUnary, recursorUnary, authorizedUnary, normalizationUnary,
      handoffUnary, normalizationAuditHandoff, handoffPkg⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
