import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_root_budget_package [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name tailRead
      budgetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index tail tailRead ->
        Cont tail transports budgetRead ->
          PkgSig bundle name pkg ->
            UnaryHistory index ∧ UnaryHistory windows ∧ UnaryHistory modulus ∧
              UnaryHistory tolerance ∧ UnaryHistory tail ∧ UnaryHistory transports ∧
                UnaryHistory budgetRead ∧ Cont index windows modulus ∧
                  Cont modulus tolerance tail ∧ Cont index tail tailRead ∧
                    Cont tail transports budgetRead ∧ PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet indexTailRead tailTransportsBudget _namePkg
  obtain ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary,
    _sealRowUnary, transportsUnary, _routesUnary, _provenanceUnary, _nameUnary,
    indexWindowsModulus, modulusToleranceTail, _tailSealRowTransports,
    _transportsRoutesProvenance, packetNamePkg⟩ := packet
  have budgetReadUnary : UnaryHistory budgetRead :=
    unary_cont_closed tailUnary transportsUnary tailTransportsBudget
  exact
    ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary,
      transportsUnary, budgetReadUnary, indexWindowsModulus, modulusToleranceTail,
      indexTailRead, tailTransportsBudget, packetNamePkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
