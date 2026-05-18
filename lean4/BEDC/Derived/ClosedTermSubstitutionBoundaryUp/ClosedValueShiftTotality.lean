import BEDC.Derived.ClosedTermSubstitutionBoundaryUp

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryClosedValueShiftTotality [AskSetup] [PackageSetup]
    {source value depth shift substitution valueRead closedValueShift ledger audit nameRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont value depth valueRead ->
        Cont shift valueRead closedValueShift ->
          Cont closedValueShift value ledger ->
            Cont ledger depth audit ->
              Cont audit shift nameRead ->
                PkgSig bundle nameRead pkg ->
                  UnaryHistory value ∧ UnaryHistory depth ∧ UnaryHistory valueRead ∧
                    UnaryHistory shift ∧ UnaryHistory closedValueShift ∧ UnaryHistory ledger ∧
                      UnaryHistory audit ∧ UnaryHistory nameRead ∧
                        Cont value depth valueRead ∧
                          Cont shift valueRead closedValueShift ∧
                            Cont closedValueShift value ledger ∧ Cont ledger depth audit ∧
                              Cont audit shift nameRead ∧ PkgSig bundle nameRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro classifier valueDepthRead shiftValueReadClosed closedValueLedger ledgerDepthAudit
    auditShiftName namePkg
  obtain ⟨_sourceUnary, valueUnary, depthUnary, shiftUnary, _substitutionUnary,
    _sourceValueShift, _shiftDepthSubstitution⟩ := classifier
  have valueReadUnary : UnaryHistory valueRead :=
    unary_cont_closed valueUnary depthUnary valueDepthRead
  have closedValueShiftUnary : UnaryHistory closedValueShift :=
    unary_cont_closed shiftUnary valueReadUnary shiftValueReadClosed
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed closedValueShiftUnary valueUnary closedValueLedger
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed ledgerUnary depthUnary ledgerDepthAudit
  have nameReadUnary : UnaryHistory nameRead :=
    unary_cont_closed auditUnary shiftUnary auditShiftName
  exact
    ⟨valueUnary, depthUnary, valueReadUnary, shiftUnary, closedValueShiftUnary, ledgerUnary,
      auditUnary, nameReadUnary, valueDepthRead, shiftValueReadClosed, closedValueLedger,
      ledgerDepthAudit, auditShiftName, namePkg⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
