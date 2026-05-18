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

theorem ClosedTermSubstitutionBoundaryOperationRowDeterminacy [AskSetup] [PackageSetup]
    {source value depth shift substitution shiftRead substitutionRead ledger audit route
      consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution →
      Cont source value shiftRead →
        Cont shiftRead depth substitutionRead →
          Cont shift substitution ledger →
            Cont substitution depth audit →
              Cont ledger audit route →
                Cont route audit consumer →
                  PkgSig bundle consumer pkg →
                    hsame shiftRead shift ∧ hsame substitutionRead substitution ∧
                      UnaryHistory ledger ∧ UnaryHistory audit ∧ UnaryHistory route ∧
                        UnaryHistory consumer ∧ Cont shift substitution ledger ∧
                          Cont substitution depth audit ∧ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro classifier sourceValueShiftRead shiftReadDepthSubstitutionRead
    shiftSubstitutionLedger substitutionDepthAudit ledgerAuditRoute routeAuditConsumer consumerPkg
  obtain ⟨sameShiftRead, sameSubstitutionRead, _sourceUnary, shiftReadUnary,
    substitutionReadUnary⟩ :=
    ClosedTermSubstitutionBoundarySourceClosednessAdmission classifier sourceValueShiftRead
      shiftReadDepthSubstitutionRead
  obtain ⟨_sourceUnary, _valueUnary, depthUnary, _shiftUnary, _substitutionUnary,
    _sourceValueShift, _shiftDepthSubstitution⟩ := classifier
  have shiftUnary : UnaryHistory shift :=
    unary_transport shiftReadUnary sameShiftRead
  have substitutionUnary : UnaryHistory substitution :=
    unary_transport substitutionReadUnary sameSubstitutionRead
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed shiftUnary substitutionUnary shiftSubstitutionLedger
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed substitutionUnary depthUnary substitutionDepthAudit
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary auditUnary ledgerAuditRoute
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed routeUnary auditUnary routeAuditConsumer
  exact
    ⟨sameShiftRead, sameSubstitutionRead, ledgerUnary, auditUnary, routeUnary,
      consumerUnary, shiftSubstitutionLedger, substitutionDepthAudit, consumerPkg⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
