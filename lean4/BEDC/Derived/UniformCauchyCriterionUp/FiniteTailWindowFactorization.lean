import BEDC.Derived.FiniteTailFilterUp
import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.FiniteTailFilterUp

theorem UniformCauchyCriterionPacket_finite_tail_window_factorization [AskSetup]
    [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name budget
      filterRead finiteSeal realRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg →
      FiniteTailFilterCarrier windows tolerance tail budget filterRead sealRow transports routes
        provenance name →
        Cont filterRead sealRow finiteSeal →
          Cont finiteSeal transports realRead →
            Cont realRead routes completionRead →
              PkgSig bundle finiteSeal pkg →
                PkgSig bundle completionRead pkg →
                  UnaryHistory windows ∧ UnaryHistory tolerance ∧ UnaryHistory tail ∧
                    UnaryHistory filterRead ∧ UnaryHistory finiteSeal ∧
                      UnaryHistory realRead ∧ UnaryHistory completionRead ∧
                        Cont windows tolerance tail ∧ Cont tail budget filterRead ∧
                          Cont filterRead sealRow finiteSeal ∧
                            Cont finiteSeal transports realRead ∧
                              Cont realRead routes completionRead ∧ hsame name sealRow ∧
                                PkgSig bundle name pkg ∧
                                  PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet filter filterSealRoute sealTransportRoute realCompletionRoute _finiteSealPkg
    completionPkg
  obtain ⟨_indexUnary, windowsUnary, _modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
    transportsUnary, routesUnary, _provenanceUnary, _nameUnary, _indexWindowsModulus,
    _modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  obtain ⟨_filterWindowsUnary, _filterToleranceUnary, budgetUnary, _filterSealUnary,
    _filterTransportsUnary, _filterRoutesUnary, windowsToleranceTail, tailBudgetFilterRead,
    nameSeal⟩ :=
    filter
  have filterReadUnary : UnaryHistory filterRead :=
    unary_cont_closed tailUnary budgetUnary tailBudgetFilterRead
  have finiteSealUnary : UnaryHistory finiteSeal :=
    unary_cont_closed filterReadUnary sealRowUnary filterSealRoute
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed finiteSealUnary transportsUnary sealTransportRoute
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed realReadUnary routesUnary realCompletionRoute
  exact
    ⟨windowsUnary, toleranceUnary, tailUnary, filterReadUnary, finiteSealUnary,
      realReadUnary, completionReadUnary, windowsToleranceTail, tailBudgetFilterRead,
      filterSealRoute, sealTransportRoute, realCompletionRoute, nameSeal, namePkg,
      completionPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
