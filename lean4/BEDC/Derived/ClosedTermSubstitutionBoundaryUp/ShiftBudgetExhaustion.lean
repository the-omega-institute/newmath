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

theorem ClosedTermSubstitutionBoundaryShiftBudgetExhaustion [AskSetup] [PackageSetup]
    {source value depth shift substitution budgetRead ledger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryClassifier source value depth shift substitution ->
      Cont source depth budgetRead ->
        Cont shift substitution ledger ->
          PkgSig bundle ledger pkg ->
            UnaryHistory source ∧ UnaryHistory depth ∧ UnaryHistory shift ∧
              UnaryHistory budgetRead ∧ UnaryHistory ledger ∧ Cont source value shift ∧
                Cont source depth budgetRead ∧ Cont shift substitution ledger ∧
                  PkgSig bundle ledger pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro classifier sourceDepthBudget shiftSubstitutionLedger ledgerPkg
  obtain ⟨sourceUnary, _valueUnary, depthUnary, shiftUnary, substitutionUnary,
    sourceValueShift, _shiftDepthSubstitution⟩ := classifier
  have budgetReadUnary : UnaryHistory budgetRead :=
    unary_cont_closed sourceUnary depthUnary sourceDepthBudget
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed shiftUnary substitutionUnary shiftSubstitutionLedger
  exact
    ⟨sourceUnary, depthUnary, shiftUnary, budgetReadUnary, ledgerUnary, sourceValueShift,
      sourceDepthBudget, shiftSubstitutionLedger, ledgerPkg⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
