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

theorem UniformCauchyCriterionPacket_finite_tail_filter_alignment [AskSetup]
    [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name budget
      filterRead filterTransport filterRoute filterPkgRow filterName sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg →
      FiniteTailFilterCarrier windows tolerance tail budget filterRead sealRow filterTransport
        filterRoute filterPkgRow filterName →
        Cont filterRead sealRow sealRead →
          PkgSig bundle sealRead pkg →
            UnaryHistory windows ∧ UnaryHistory tolerance ∧ UnaryHistory tail ∧
              UnaryHistory filterRead ∧ UnaryHistory sealRow ∧ UnaryHistory sealRead ∧
                Cont windows tolerance tail ∧ Cont tail budget filterRead ∧
                  Cont filterRead sealRow sealRead ∧ hsame filterName sealRow ∧
                    PkgSig bundle name pkg ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame PkgSig UnaryHistory
  intro packet filter sealReadRoute sealReadPkg
  obtain ⟨_indexUnary, windowsUnary, _modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, _indexWindowsModulus,
    _modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance,
    namePkg⟩ := packet
  obtain ⟨_filterWindowsUnary, _filterToleranceUnary, budgetUnary, _filterSealUnary,
    _filterTransportUnary, _filterRouteUnary, windowsToleranceTail, tailBudgetFilterRead,
    filterNameSameSeal⟩ := filter
  have filterReadUnary : UnaryHistory filterRead :=
    unary_cont_closed tailUnary budgetUnary tailBudgetFilterRead
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed filterReadUnary sealRowUnary sealReadRoute
  exact
    ⟨windowsUnary, toleranceUnary, tailUnary, filterReadUnary, sealRowUnary, sealReadUnary,
      windowsToleranceTail, tailBudgetFilterRead, sealReadRoute, filterNameSameSeal, namePkg,
      sealReadPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
