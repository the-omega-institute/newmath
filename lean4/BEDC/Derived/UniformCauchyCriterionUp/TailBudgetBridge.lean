import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_tail_budget_bridge [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name tailBudget
      sealRead realWindow realSealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg →
      Cont index tail tailBudget →
        Cont tail sealRow sealRead →
          Cont windows tail realWindow →
            hsame tail realWindow →
              Cont realWindow sealRow realSealRead →
                PkgSig bundle tailBudget pkg →
                  PkgSig bundle sealRead pkg →
                    PkgSig bundle realSealRead pkg →
                      UnaryHistory tailBudget ∧ UnaryHistory sealRead ∧
                        UnaryHistory realWindow ∧ UnaryHistory realSealRead ∧
                          hsame sealRead realSealRead ∧ Cont index tail tailBudget ∧
                            Cont tail sealRow sealRead ∧ Cont windows tail realWindow ∧
                              Cont realWindow sealRow realSealRead ∧ PkgSig bundle name pkg ∧
                                PkgSig bundle tailBudget pkg ∧ PkgSig bundle sealRead pkg ∧
                                  PkgSig bundle realSealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro packet indexTailBudget tailSealRead windowsTailRealWindow sameTailRealWindow
    realWindowSealRead tailBudgetPkg sealReadPkg realSealReadPkg
  obtain ⟨indexUnary, windowsUnary, _modulusUnary, _toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, _indexWindowsModulus,
    _modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have tailBudgetUnary : UnaryHistory tailBudget :=
    unary_cont_closed indexUnary tailUnary indexTailBudget
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealRead
  have realWindowUnary : UnaryHistory realWindow :=
    unary_cont_closed windowsUnary tailUnary windowsTailRealWindow
  have realSealReadUnary : UnaryHistory realSealRead :=
    unary_cont_closed realWindowUnary sealRowUnary realWindowSealRead
  have sealReadsSame : hsame sealRead realSealRead :=
    cont_respects_hsame sameTailRealWindow (hsame_refl sealRow) tailSealRead realWindowSealRead
  exact
    ⟨tailBudgetUnary, sealReadUnary, realWindowUnary, realSealReadUnary, sealReadsSame,
      indexTailBudget, tailSealRead, windowsTailRealWindow, realWindowSealRead, namePkg,
      tailBudgetPkg, sealReadPkg, realSealReadPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
