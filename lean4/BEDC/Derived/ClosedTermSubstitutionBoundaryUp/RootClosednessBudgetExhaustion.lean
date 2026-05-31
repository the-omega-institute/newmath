import BEDC.Derived.ClosedTermSubstitutionBoundaryUp

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryRootClosednessBudgetExhaustion [AskSetup] [PackageSetup]
    {source value depth shift substitution shiftRead substitutionRead ledger audit rootRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont source value shiftRead ->
        Cont shiftRead depth substitutionRead ->
          Cont shift substitution ledger ->
            Cont substitution depth audit ->
              Cont audit ledger rootRead ->
                PkgSig bundle rootRead pkg ->
                  hsame shiftRead shift ∧ hsame substitutionRead substitution ∧
                    UnaryHistory source ∧ UnaryHistory value ∧ UnaryHistory depth ∧
                      UnaryHistory ledger ∧ UnaryHistory audit ∧ UnaryHistory rootRead ∧
                        PkgSig bundle rootRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro classifier sourceValueShiftRead shiftReadDepthSubstitutionRead
    shiftSubstitutionLedger substitutionDepthAudit auditLedgerRootRead rootReadPkg
  obtain ⟨sourceUnary, valueUnary, depthUnary, shiftUnary, substitutionUnary,
    sourceValueShift, shiftDepthSubstitution⟩ := classifier
  have sameShiftRead : hsame shiftRead shift :=
    cont_deterministic sourceValueShiftRead sourceValueShift
  have sameSubstitutionRead : hsame substitutionRead substitution :=
    cont_respects_hsame sameShiftRead (hsame_refl depth) shiftReadDepthSubstitutionRead
      shiftDepthSubstitution
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed shiftUnary substitutionUnary shiftSubstitutionLedger
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed substitutionUnary depthUnary substitutionDepthAudit
  have rootReadUnary : UnaryHistory rootRead :=
    unary_cont_closed auditUnary ledgerUnary auditLedgerRootRead
  exact
    ⟨sameShiftRead, sameSubstitutionRead, sourceUnary, valueUnary, depthUnary, ledgerUnary,
      auditUnary, rootReadUnary, rootReadPkg⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
