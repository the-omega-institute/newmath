import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_cauchy_limit_functor_terminal_handoff
    [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name tailRead
      sealRead sealBudgetRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg →
      Cont index tail tailRead →
        Cont tail sealRow sealRead →
          Cont tailRead sealRead sealBudgetRead →
            Cont sealBudgetRead name completionRead →
              PkgSig bundle tailRead pkg →
                PkgSig bundle sealRead pkg →
                  PkgSig bundle sealBudgetRead pkg →
                    PkgSig bundle completionRead pkg →
                      UnaryHistory index ∧ UnaryHistory windows ∧ UnaryHistory modulus ∧
                        UnaryHistory tolerance ∧ UnaryHistory tail ∧ UnaryHistory sealRow ∧
                          UnaryHistory tailRead ∧ UnaryHistory sealRead ∧
                            UnaryHistory sealBudgetRead ∧ UnaryHistory completionRead ∧
                              Cont index windows modulus ∧ Cont modulus tolerance tail ∧
                                Cont index tail tailRead ∧ Cont tail sealRow sealRead ∧
                                  Cont tailRead sealRead sealBudgetRead ∧
                                    Cont sealBudgetRead name completionRead ∧
                                      PkgSig bundle name pkg ∧ PkgSig bundle tailRead pkg ∧
                                        PkgSig bundle sealRead pkg ∧
                                          PkgSig bundle sealBudgetRead pkg ∧
                                            PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet indexTailRead tailSealRead tailSealBudgetRead budgetNameCompletion
    tailReadPkg sealReadPkg sealBudgetPkg completionPkg
  obtain ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, nameUnary, indexWindowsModulus,
    modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed indexUnary tailUnary indexTailRead
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealRead
  have sealBudgetUnary : UnaryHistory sealBudgetRead :=
    unary_cont_closed tailReadUnary sealReadUnary tailSealBudgetRead
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed sealBudgetUnary nameUnary budgetNameCompletion
  exact
    ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
      tailReadUnary, sealReadUnary, sealBudgetUnary, completionUnary, indexWindowsModulus,
      modulusToleranceTail, indexTailRead, tailSealRead, tailSealBudgetRead,
      budgetNameCompletion, namePkg, tailReadPkg, sealReadPkg, sealBudgetPkg,
      completionPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
