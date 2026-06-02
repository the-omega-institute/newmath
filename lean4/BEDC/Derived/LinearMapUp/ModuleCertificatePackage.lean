import BEDC.Derived.LinearMapUp
import BEDC.FKernel.Unary

namespace BEDC.Derived.LinearMapUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def ModuleLinearMapCertificatePackage
    (source target function output additive scalar zero ledger : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory output ∧
    UnaryHistory additive ∧ Cont function source output ∧ Cont output additive scalar ∧
      Cont scalar zero ledger ∧ hsame zero BHist.Empty

theorem ModuleLinearMapCertificatePackage_exactness
    {source target function output additive scalar zero ledger : BHist} :
    ModuleLinearMapCertificatePackage source target function output additive scalar zero ledger ->
      UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory output ∧
        UnaryHistory ledger ∧ Cont function source output ∧ Cont output additive scalar ∧
          Cont scalar zero ledger ∧ hsame zero BHist.Empty := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro package
  obtain ⟨sourceUnary, targetUnary, outputUnary, additiveUnary, functionRoute, additiveRoute,
    ledgerRoute, zeroEmpty⟩ := package
  cases zeroEmpty
  have zeroUnary : UnaryHistory BHist.Empty := unary_empty
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed
      (unary_cont_closed outputUnary additiveUnary additiveRoute)
      zeroUnary
      ledgerRoute
  exact
    ⟨sourceUnary, targetUnary, outputUnary, ledgerUnary, functionRoute, additiveRoute,
      ledgerRoute, hsame_refl BHist.Empty⟩

end BEDC.Derived.LinearMapUp
