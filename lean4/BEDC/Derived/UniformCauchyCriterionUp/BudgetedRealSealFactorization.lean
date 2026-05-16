import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_budgeted_real_seal_factorization [AskSetup]
    [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name tailRead
      sealRead budgetRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg →
      Cont index tail tailRead →
        Cont tail sealRow sealRead →
          Cont tailRead sealRead budgetRead →
            Cont budgetRead sealRead realRead →
              PkgSig bundle tailRead pkg →
                PkgSig bundle sealRead pkg →
                  PkgSig bundle budgetRead pkg →
                    PkgSig bundle realRead pkg →
                      UnaryHistory tailRead ∧ UnaryHistory sealRead ∧
                        UnaryHistory budgetRead ∧ UnaryHistory realRead ∧
                          Cont index windows modulus ∧ Cont modulus tolerance tail ∧
                            Cont tailRead sealRead budgetRead ∧
                              Cont budgetRead sealRead realRead ∧ PkgSig bundle name pkg ∧
                                PkgSig bundle budgetRead pkg ∧ PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet indexTailRead tailSealRead tailReadSealBudget budgetSealReal _tailPkg
    _sealPkg budgetPkg realPkg
  obtain ⟨indexUnary, _windowsUnary, _modulusUnary, _toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, indexWindowsModulus,
    modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed indexUnary tailUnary indexTailRead
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealRead
  have budgetReadUnary : UnaryHistory budgetRead :=
    unary_cont_closed tailReadUnary sealReadUnary tailReadSealBudget
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed budgetReadUnary sealReadUnary budgetSealReal
  exact
    ⟨tailReadUnary, sealReadUnary, budgetReadUnary, realReadUnary, indexWindowsModulus,
      modulusToleranceTail, tailReadSealBudget, budgetSealReal, namePkg, budgetPkg, realPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
