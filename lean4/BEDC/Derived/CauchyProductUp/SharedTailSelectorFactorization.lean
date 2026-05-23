import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_shared_tail_selector_factorization [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name sharedTailRead budgetClassifier selectorRead
      combinedRead finalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont transport routes sharedTailRead ->
        Cont classifier routes budgetClassifier ->
          Cont budgetClassifier ledger selectorRead ->
            Cont sharedTailRead selectorRead combinedRead ->
              Cont combinedRead ledger finalRead ->
                PkgSig bundle finalRead pkg ->
                  UnaryHistory transport ∧ UnaryHistory sharedTailRead ∧
                    UnaryHistory product ∧ UnaryHistory classifier ∧
                      UnaryHistory budgetClassifier ∧ UnaryHistory selectorRead ∧
                        UnaryHistory combinedRead ∧ UnaryHistory finalRead ∧
                          Cont transport routes sharedTailRead ∧
                            Cont classifier routes budgetClassifier ∧
                              Cont budgetClassifier ledger selectorRead ∧
                                Cont sharedTailRead selectorRead combinedRead ∧
                                  Cont combinedRead ledger finalRead ∧ PkgSig bundle name pkg ∧
                                    PkgSig bundle finalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet transportSharedTail classifierBudget budgetSelector sharedSelectorCombined
    combinedFinal finalReadPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, windowAUnary, windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed windowAUnary windowBUnary windowTransport
  have sharedTailUnary : UnaryHistory sharedTailRead :=
    unary_cont_closed transportUnary routesUnary transportSharedTail
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have budgetClassifierUnary : UnaryHistory budgetClassifier :=
    unary_cont_closed classifierUnary routesUnary classifierBudget
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed budgetClassifierUnary ledgerUnary budgetSelector
  have combinedUnary : UnaryHistory combinedRead :=
    unary_cont_closed sharedTailUnary selectorUnary sharedSelectorCombined
  have finalUnary : UnaryHistory finalRead :=
    unary_cont_closed combinedUnary ledgerUnary combinedFinal
  exact
    ⟨transportUnary, sharedTailUnary, productUnary, classifierUnary, budgetClassifierUnary,
      selectorUnary, combinedUnary, finalUnary, transportSharedTail, classifierBudget,
      budgetSelector, sharedSelectorCombined, combinedFinal, namePkg, finalReadPkg⟩

end BEDC.Derived.CauchyProductUp
