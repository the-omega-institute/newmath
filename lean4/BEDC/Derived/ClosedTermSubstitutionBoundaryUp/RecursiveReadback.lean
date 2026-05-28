import BEDC.Derived.ClosedTermSubstitutionBoundaryUp

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryRecursiveReadback [AskSetup] [PackageSetup]
    {source value depth shift substitution ledger audit route consumer branch compiler : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont shift substitution ledger ->
        Cont substitution depth audit ->
          Cont ledger audit route ->
            Cont route audit consumer ->
              Cont consumer ledger branch ->
                Cont branch audit compiler ->
                  PkgSig bundle compiler pkg ->
                    UnaryHistory ledger ∧ UnaryHistory audit ∧ UnaryHistory route ∧
                      UnaryHistory consumer ∧ UnaryHistory branch ∧ UnaryHistory compiler ∧
                        Cont shift substitution ledger ∧ Cont substitution depth audit ∧
                          Cont ledger audit route ∧ Cont route audit consumer ∧
                            Cont consumer ledger branch ∧ Cont branch audit compiler ∧
                              PkgSig bundle compiler pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro classifier shiftSubstitutionLedger substitutionDepthAudit ledgerAuditRoute
    routeAuditConsumer consumerLedgerBranch branchAuditCompiler compilerPkg
  obtain ⟨_sourceUnary, _valueUnary, depthUnary, shiftUnary, substitutionUnary,
    _sourceValueShift, _shiftDepthSubstitution⟩ := classifier
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed shiftUnary substitutionUnary shiftSubstitutionLedger
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed substitutionUnary depthUnary substitutionDepthAudit
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary auditUnary ledgerAuditRoute
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed routeUnary auditUnary routeAuditConsumer
  have branchUnary : UnaryHistory branch :=
    unary_cont_closed consumerUnary ledgerUnary consumerLedgerBranch
  have compilerUnary : UnaryHistory compiler :=
    unary_cont_closed branchUnary auditUnary branchAuditCompiler
  exact
    ⟨ledgerUnary, auditUnary, routeUnary, consumerUnary, branchUnary, compilerUnary,
      shiftSubstitutionLedger, substitutionDepthAudit, ledgerAuditRoute, routeAuditConsumer,
      consumerLedgerBranch, branchAuditCompiler, compilerPkg⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
