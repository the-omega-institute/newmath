import BEDC.Derived.ClosedTermSubstitutionBoundaryUp

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryClosednessConsumerExport [AskSetup] [PackageSetup]
    {source value depth shift substitution sourceClosed valueClosed ledger audit exportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont source value sourceClosed ->
        Cont value depth valueClosed ->
          Cont sourceClosed valueClosed ledger ->
            Cont ledger shift audit ->
              Cont audit substitution exportRead ->
                PkgSig bundle exportRead pkg ->
                  UnaryHistory sourceClosed ∧ UnaryHistory valueClosed ∧
                    UnaryHistory ledger ∧ UnaryHistory audit ∧ UnaryHistory exportRead ∧
                      Cont sourceClosed valueClosed ledger ∧ Cont ledger shift audit ∧
                        Cont audit substitution exportRead ∧ PkgSig bundle exportRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro classifier sourceValueClosed valueDepthClosed closednessLedger ledgerShiftAudit
    auditSubstitutionExport exportPkg
  obtain ⟨sourceUnary, valueUnary, depthUnary, shiftUnary, substitutionUnary,
    _sourceValueShift, _shiftDepthSubstitution⟩ := classifier
  have sourceClosedUnary : UnaryHistory sourceClosed :=
    unary_cont_closed sourceUnary valueUnary sourceValueClosed
  have valueClosedUnary : UnaryHistory valueClosed :=
    unary_cont_closed valueUnary depthUnary valueDepthClosed
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed sourceClosedUnary valueClosedUnary closednessLedger
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed ledgerUnary shiftUnary ledgerShiftAudit
  have exportUnary : UnaryHistory exportRead :=
    unary_cont_closed auditUnary substitutionUnary auditSubstitutionExport
  exact
    ⟨sourceClosedUnary, valueClosedUnary, ledgerUnary, auditUnary, exportUnary,
      closednessLedger, ledgerShiftAudit, auditSubstitutionExport, exportPkg⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
