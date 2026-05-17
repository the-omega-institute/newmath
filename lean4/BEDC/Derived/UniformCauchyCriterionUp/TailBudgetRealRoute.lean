import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_tail_budget_real_route [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name tailRead
      realRead budgetRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index tail tailRead ->
        Cont tail sealRow realRead ->
          Cont tailRead realRead budgetRoute ->
            PkgSig bundle tailRead pkg ->
              PkgSig bundle realRead pkg ->
                PkgSig bundle budgetRoute pkg ->
                  UnaryHistory index ∧ UnaryHistory tail ∧ UnaryHistory sealRow ∧
                    UnaryHistory tailRead ∧ UnaryHistory realRead ∧
                      UnaryHistory budgetRoute ∧ Cont index tail tailRead ∧
                        Cont tail sealRow realRead ∧ Cont tailRead realRead budgetRoute ∧
                          PkgSig bundle name pkg ∧ PkgSig bundle tailRead pkg ∧
                            PkgSig bundle realRead pkg ∧ PkgSig bundle budgetRoute pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet indexTailRead tailSealRead tailRealBudget tailReadPkg realReadPkg budgetPkg
  obtain ⟨indexUnary, _windowsUnary, _modulusUnary, _toleranceUnary, tailUnary,
    sealRowUnary, _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary,
    _indexWindowsModulus, _modulusToleranceTail, _tailSealRowTransports,
    _transportsRoutesProvenance, namePkg⟩ := packet
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed indexUnary tailUnary indexTailRead
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealRead
  have budgetRouteUnary : UnaryHistory budgetRoute :=
    unary_cont_closed tailReadUnary realReadUnary tailRealBudget
  exact
    ⟨indexUnary, tailUnary, sealRowUnary, tailReadUnary, realReadUnary, budgetRouteUnary,
      indexTailRead, tailSealRead, tailRealBudget, namePkg, tailReadPkg, realReadPkg,
      budgetPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
