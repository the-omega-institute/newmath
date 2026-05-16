import BEDC.Derived.UniformCauchyCriterionUp.CompletionFunctorBudget

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_regular_tail_fusion_factorization
    [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name budgetRead
      sharedTail sealRead fusionRead hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index tail budgetRead ->
        Cont budgetRead provenance sharedTail ->
          Cont sharedTail sealRow sealRead ->
            Cont sealRead name fusionRead ->
              PkgSig bundle budgetRead pkg ->
                PkgSig bundle sharedTail pkg ->
                  PkgSig bundle sealRead pkg ->
                    PkgSig bundle fusionRead pkg ->
                      UnaryHistory budgetRead ∧ UnaryHistory sharedTail ∧
                        UnaryHistory sealRead ∧ UnaryHistory fusionRead ∧
                          Cont index tail budgetRead ∧ Cont budgetRead provenance sharedTail ∧
                            Cont sharedTail sealRow sealRead ∧ Cont sealRead name fusionRead ∧
                              PkgSig bundle name pkg ∧ PkgSig bundle fusionRead pkg ∧
                                (Cont fusionRead (BHist.e0 hostTail) index -> False) ∧
                                  (Cont fusionRead (BHist.e1 hostTail) index -> False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet indexTailBudget budgetProvenanceShared sharedSealRead sealNameFusion
    _budgetPkg _sharedPkg _sealPkg fusionPkg
  obtain ⟨indexUnary, _windowsUnary, _modulusUnary, _toleranceUnary, tailUnary,
    sealRowUnary, _transportsUnary, _routesUnary, provenanceUnary, nameUnary,
    _indexWindowsModulus, _modulusToleranceTail, _tailSealRowTransports,
    _transportsRoutesProvenance, namePkg⟩ := packet
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed indexUnary tailUnary indexTailBudget
  have sharedUnary : UnaryHistory sharedTail :=
    unary_cont_closed budgetUnary provenanceUnary budgetProvenanceShared
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed sharedUnary sealRowUnary sharedSealRead
  have fusionUnary : UnaryHistory fusionRead :=
    unary_cont_closed sealUnary nameUnary sealNameFusion
  have indexToFusion :
      Cont index (append tail (append provenance (append sealRow name))) fusionRead := by
    cases indexTailBudget
    cases budgetProvenanceShared
    cases sharedSealRead
    exact sealNameFusion.trans
      ((append_assoc (append (append index tail) provenance) sealRow name).trans
        ((congrArg (fun z => append z (append sealRow name))
            (append_assoc index tail provenance)).trans
          ((append_assoc index (append tail provenance) (append sealRow name)).trans
            (congrArg (fun z => append index z)
              (append_assoc tail provenance (append sealRow name))))))
  exact
    ⟨budgetUnary, sharedUnary, sealUnary, fusionUnary, indexTailBudget,
      budgetProvenanceShared, sharedSealRead, sealNameFusion, namePkg, fusionPkg,
      (fun hostReturn =>
        cont_mutual_extension_right_tail_absurd.left indexToFusion hostReturn),
      (fun hostReturn =>
        cont_mutual_extension_right_tail_absurd.right indexToFusion hostReturn)⟩

end BEDC.Derived.UniformCauchyCriterionUp
