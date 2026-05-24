import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_root_window_factorization [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name budgetEntry : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont classifier routes budgetEntry ->
        PkgSig bundle budgetEntry pkg ->
          UnaryHistory windowA ∧ UnaryHistory windowB ∧ UnaryHistory radiusA ∧
            UnaryHistory radiusB ∧ UnaryHistory observationA ∧ UnaryHistory observationB ∧
              UnaryHistory product ∧ UnaryHistory classifier ∧ UnaryHistory budgetEntry ∧
                Cont windowA windowB transport ∧ Cont observationA observationB product ∧
                  Cont product ledger classifier ∧ Cont classifier routes budgetEntry ∧
                    PkgSig bundle name pkg ∧ PkgSig bundle budgetEntry pkg := by
  -- BEDC touchpoint anchor: CauchyProductPacket BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet classifierBudget budgetEntryPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, windowAUnary, windowBUnary, radiusAUnary,
    radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have budgetEntryUnary : UnaryHistory budgetEntry :=
    unary_cont_closed classifierUnary routesUnary classifierBudget
  exact
    ⟨windowAUnary, windowBUnary, radiusAUnary, radiusBUnary, observationAUnary,
      observationBUnary, productUnary, classifierUnary, budgetEntryUnary, windowTransport,
      productRoute, classifierRoute, classifierBudget, namePkg, budgetEntryPkg⟩

end BEDC.Derived.CauchyProductUp
