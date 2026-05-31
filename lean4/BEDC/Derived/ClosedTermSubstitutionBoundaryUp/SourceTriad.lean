import BEDC.Derived.ClosedTermSubstitutionBoundaryUp

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundarySourceTriad [AskSetup] [PackageSetup]
    {source value depth shift substitution sourceValueRead valueDepthRead ledger audit route :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont source value sourceValueRead ->
        Cont value depth valueDepthRead ->
          Cont shift substitution ledger ->
            Cont substitution depth audit ->
              Cont ledger audit route ->
                PkgSig bundle route pkg ->
                  UnaryHistory source ∧ UnaryHistory value ∧ UnaryHistory depth ∧
                    UnaryHistory sourceValueRead ∧ UnaryHistory valueDepthRead ∧
                      UnaryHistory ledger ∧ UnaryHistory audit ∧ UnaryHistory route ∧
                        Cont source value sourceValueRead ∧ Cont value depth valueDepthRead ∧
                          Cont shift substitution ledger ∧ Cont substitution depth audit ∧
                            Cont ledger audit route ∧ PkgSig bundle route pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro classifier sourceValueAdmission valueDepthAdmission shiftSubstitutionLedger
    substitutionDepthAudit ledgerAuditRoute routePkg
  obtain ⟨sourceUnary, valueUnary, depthUnary, shiftUnary, substitutionUnary,
    _sourceValueShift, _shiftDepthSubstitution⟩ := classifier
  have sourceValueReadUnary : UnaryHistory sourceValueRead :=
    unary_cont_closed sourceUnary valueUnary sourceValueAdmission
  have valueDepthReadUnary : UnaryHistory valueDepthRead :=
    unary_cont_closed valueUnary depthUnary valueDepthAdmission
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed shiftUnary substitutionUnary shiftSubstitutionLedger
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed substitutionUnary depthUnary substitutionDepthAudit
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary auditUnary ledgerAuditRoute
  exact
    ⟨sourceUnary, valueUnary, depthUnary, sourceValueReadUnary, valueDepthReadUnary,
      ledgerUnary, auditUnary, routeUnary, sourceValueAdmission, valueDepthAdmission,
      shiftSubstitutionLedger, substitutionDepthAudit, ledgerAuditRoute, routePkg⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
