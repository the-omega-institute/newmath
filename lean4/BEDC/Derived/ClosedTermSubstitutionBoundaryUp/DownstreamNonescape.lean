import BEDC.Derived.ClosedTermSubstitutionBoundaryUp

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryDownstreamNonescape [AskSetup] [PackageSetup]
    {source value depth shift substitution ledger audit route sourceRead branch compiler
      downstream : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont shift substitution ledger ->
        Cont substitution depth audit ->
          Cont ledger audit route ->
            Cont route audit sourceRead ->
              Cont sourceRead ledger branch ->
                Cont branch audit compiler ->
                  Cont compiler sourceRead downstream ->
                    PkgSig bundle downstream pkg ->
                      UnaryHistory ledger ∧ UnaryHistory audit ∧ UnaryHistory route ∧
                        UnaryHistory sourceRead ∧ UnaryHistory branch ∧
                          UnaryHistory compiler ∧ UnaryHistory downstream ∧
                            Cont compiler sourceRead downstream ∧
                              PkgSig bundle downstream pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro classifier shiftSubstitutionLedger substitutionDepthAudit ledgerAuditRoute
    routeAuditSourceRead sourceReadLedgerBranch branchAuditCompiler
    compilerSourceReadDownstream downstreamPkg
  obtain ⟨_sourceUnary, _valueUnary, depthUnary, shiftUnary, substitutionUnary,
    _sourceValueShift, _shiftDepthSubstitution⟩ := classifier
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed shiftUnary substitutionUnary shiftSubstitutionLedger
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed substitutionUnary depthUnary substitutionDepthAudit
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary auditUnary ledgerAuditRoute
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed routeUnary auditUnary routeAuditSourceRead
  have branchUnary : UnaryHistory branch :=
    unary_cont_closed sourceReadUnary ledgerUnary sourceReadLedgerBranch
  have compilerUnary : UnaryHistory compiler :=
    unary_cont_closed branchUnary auditUnary branchAuditCompiler
  have downstreamUnary : UnaryHistory downstream :=
    unary_cont_closed compilerUnary sourceReadUnary compilerSourceReadDownstream
  exact
    ⟨ledgerUnary, auditUnary, routeUnary, sourceReadUnary, branchUnary, compilerUnary,
      downstreamUnary, compilerSourceReadDownstream, downstreamPkg⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
