import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_real_completion_budget_lock [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name tailRead
      sealRead sealBudgetRead completionRead hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg →
      Cont index tail tailRead →
        Cont tail sealRow sealRead →
          Cont tailRead sealRead sealBudgetRead →
            Cont sealBudgetRead provenance completionRead →
              PkgSig bundle tailRead pkg →
                PkgSig bundle sealRead pkg →
                  PkgSig bundle sealBudgetRead pkg →
                    PkgSig bundle completionRead pkg →
                      UnaryHistory completionRead ∧ Cont index windows modulus ∧
                        Cont modulus tolerance tail ∧ Cont index tail tailRead ∧
                          Cont tail sealRow sealRead ∧
                            Cont tailRead sealRead sealBudgetRead ∧
                              Cont sealBudgetRead provenance completionRead ∧
                                PkgSig bundle name pkg ∧ PkgSig bundle completionRead pkg ∧
                                  (Cont sealBudgetRead (BHist.e0 hostTail) tailRead →
                                    False) ∧
                                    (Cont sealBudgetRead (BHist.e1 hostTail) tailRead →
                                      False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet indexTailRead tailSealRead readSealBudget budgetProvenanceCompletion
    _tailReadPkg _sealReadPkg _budgetPkg completionPkg
  obtain ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, provenanceUnary, _nameUnary, indexWindowsModulus,
    modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed indexUnary tailUnary indexTailRead
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealRead
  have budgetUnary : UnaryHistory sealBudgetRead :=
    unary_cont_closed tailReadUnary sealReadUnary readSealBudget
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed budgetUnary provenanceUnary budgetProvenanceCompletion
  exact
    ⟨completionUnary, indexWindowsModulus, modulusToleranceTail, indexTailRead, tailSealRead,
      readSealBudget, budgetProvenanceCompletion, namePkg, completionPkg,
      (fun hostReturn =>
        cont_mutual_extension_right_tail_absurd.left readSealBudget hostReturn),
      (fun hostReturn =>
        cont_mutual_extension_right_tail_absurd.right readSealBudget hostReturn)⟩

end BEDC.Derived.UniformCauchyCriterionUp
