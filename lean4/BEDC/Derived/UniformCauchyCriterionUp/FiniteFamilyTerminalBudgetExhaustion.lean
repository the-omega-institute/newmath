import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_finite_family_terminal_budget_exhaustion
    [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name tailRead
      sealRead sealBudgetRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index tail tailRead ->
        Cont tail sealRow sealRead ->
          Cont tailRead sealRead sealBudgetRead ->
            Cont sealBudgetRead provenance terminalRead ->
              PkgSig bundle tailRead pkg ->
                PkgSig bundle sealRead pkg ->
                  PkgSig bundle sealBudgetRead pkg ->
                    PkgSig bundle terminalRead pkg ->
                      UnaryHistory index ∧ UnaryHistory windows ∧ UnaryHistory modulus ∧
                        UnaryHistory tolerance ∧ UnaryHistory tail ∧ UnaryHistory sealRow ∧
                          UnaryHistory tailRead ∧ UnaryHistory sealRead ∧
                            UnaryHistory sealBudgetRead ∧ UnaryHistory terminalRead ∧
                              Cont index windows modulus ∧ Cont modulus tolerance tail ∧
                                Cont index tail tailRead ∧ Cont tail sealRow sealRead ∧
                                  Cont tailRead sealRead sealBudgetRead ∧
                                    Cont sealBudgetRead provenance terminalRead ∧
                                      PkgSig bundle name pkg ∧ PkgSig bundle tailRead pkg ∧
                                        PkgSig bundle sealRead pkg ∧
                                          PkgSig bundle sealBudgetRead pkg ∧
                                            PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet indexTailRead tailSealRead readSealBudget budgetProvenance tailReadPkg
    sealReadPkg budgetPkg terminalPkg
  obtain ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealUnary,
    _transportsUnary, _routesUnary, provenanceUnary, _nameUnary, indexWindowsModulus,
    modulusToleranceTail, _tailSealTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed indexUnary tailUnary indexTailRead
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary sealUnary tailSealRead
  have budgetUnary : UnaryHistory sealBudgetRead :=
    unary_cont_closed tailReadUnary sealReadUnary readSealBudget
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed budgetUnary provenanceUnary budgetProvenance
  exact
    ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealUnary,
      tailReadUnary, sealReadUnary, budgetUnary, terminalUnary, indexWindowsModulus,
      modulusToleranceTail, indexTailRead, tailSealRead, readSealBudget, budgetProvenance,
      namePkg, tailReadPkg, sealReadPkg, budgetPkg, terminalPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
