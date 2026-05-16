import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_root_real_completion_exit_exhaustion [AskSetup]
    [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name tailRead
      sealRead sealBudgetRead completionRead phaseRead hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg →
      Cont index tail tailRead →
        Cont tail sealRow sealRead →
          Cont tailRead sealRead sealBudgetRead →
            Cont sealBudgetRead provenance completionRead →
              Cont completionRead name phaseRead →
                PkgSig bundle tailRead pkg →
                  PkgSig bundle sealRead pkg →
                    PkgSig bundle sealBudgetRead pkg →
                      PkgSig bundle completionRead pkg →
                        PkgSig bundle phaseRead pkg →
                          UnaryHistory index ∧ UnaryHistory windows ∧ UnaryHistory modulus ∧
                            UnaryHistory tolerance ∧ UnaryHistory tail ∧
                              UnaryHistory sealRow ∧ UnaryHistory completionRead ∧
                                UnaryHistory phaseRead ∧ Cont index windows modulus ∧
                                  Cont modulus tolerance tail ∧ Cont index tail tailRead ∧
                                    Cont tail sealRow sealRead ∧
                                      Cont tailRead sealRead sealBudgetRead ∧
                                        Cont sealBudgetRead provenance completionRead ∧
                                          Cont completionRead name phaseRead ∧
                                            PkgSig bundle name pkg ∧
                                              PkgSig bundle phaseRead pkg ∧
                                                (Cont sealBudgetRead (BHist.e0 hostTail)
                                                    tailRead → False) ∧
                                                  (Cont sealBudgetRead (BHist.e1 hostTail)
                                                      tailRead → False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet indexTailRead tailSealRead readSealBudget budgetProvenanceCompletion
    completionNamePhase _tailReadPkg _sealReadPkg _budgetPkg _completionPkg phasePkg
  obtain ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, provenanceUnary, nameUnary, indexWindowsModulus,
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
  have phaseUnary : UnaryHistory phaseRead :=
    unary_cont_closed completionUnary nameUnary completionNamePhase
  exact
    ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
      completionUnary, phaseUnary, indexWindowsModulus, modulusToleranceTail, indexTailRead,
      tailSealRead, readSealBudget, budgetProvenanceCompletion, completionNamePhase, namePkg,
      phasePkg,
      (fun hostReturn =>
        cont_mutual_extension_right_tail_absurd.left readSealBudget hostReturn),
      (fun hostReturn =>
        cont_mutual_extension_right_tail_absurd.right readSealBudget hostReturn)⟩

end BEDC.Derived.UniformCauchyCriterionUp
