import BEDC.Derived.ClosedTermSubstitutionBoundaryUp

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryCompilerConsumerLock [AskSetup] [PackageSetup]
    {term value depth shift substitution ledger audit route consumer compilerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier term value depth shift substitution ->
      Cont shift substitution ledger ->
        Cont substitution depth audit ->
          Cont ledger audit route ->
            Cont route audit consumer ->
              Cont consumer substitution compilerRead ->
                PkgSig bundle compilerRead pkg ->
                  UnaryHistory term ∧ UnaryHistory value ∧ UnaryHistory depth ∧
                    UnaryHistory shift ∧ UnaryHistory substitution ∧ UnaryHistory ledger ∧
                      UnaryHistory audit ∧ UnaryHistory route ∧ UnaryHistory consumer ∧
                        UnaryHistory compilerRead ∧ Cont shift substitution ledger ∧
                          Cont substitution depth audit ∧ Cont ledger audit route ∧
                            Cont route audit consumer ∧ Cont consumer substitution compilerRead ∧
                              PkgSig bundle compilerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro classifier shiftSubstitutionLedger substitutionDepthAudit ledgerAuditRoute
    routeAuditConsumer consumerSubstitutionCompilerRead compilerReadPkg
  obtain ⟨termUnary, valueUnary, depthUnary, shiftUnary, substitutionUnary,
    _termValueShift, _shiftDepthSubstitution⟩ := classifier
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed shiftUnary substitutionUnary shiftSubstitutionLedger
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed substitutionUnary depthUnary substitutionDepthAudit
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary auditUnary ledgerAuditRoute
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed routeUnary auditUnary routeAuditConsumer
  have compilerReadUnary : UnaryHistory compilerRead :=
    unary_cont_closed consumerUnary substitutionUnary consumerSubstitutionCompilerRead
  exact
    ⟨termUnary, valueUnary, depthUnary, shiftUnary, substitutionUnary, ledgerUnary, auditUnary,
      routeUnary, consumerUnary, compilerReadUnary, shiftSubstitutionLedger,
      substitutionDepthAudit, ledgerAuditRoute, routeAuditConsumer,
      consumerSubstitutionCompilerRead, compilerReadPkg⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
