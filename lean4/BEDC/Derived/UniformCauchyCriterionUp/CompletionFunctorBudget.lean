import BEDC.Derived.UniformCauchyCriterionUp.CauchyLimitFunctorTerminalHandoff

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_completion_functor_budget_handoff [AskSetup]
    [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name budgetRead
      sharedTail completionRead hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index tail budgetRead ->
        Cont budgetRead provenance sharedTail ->
          Cont sharedTail sealRow completionRead ->
            PkgSig bundle budgetRead pkg ->
              PkgSig bundle sharedTail pkg ->
                PkgSig bundle completionRead pkg ->
                  UnaryHistory budgetRead ∧ UnaryHistory sharedTail ∧
                    UnaryHistory completionRead ∧ Cont index tail budgetRead ∧
                      Cont budgetRead provenance sharedTail ∧
                        Cont sharedTail sealRow completionRead ∧
                          PkgSig bundle name pkg ∧ PkgSig bundle completionRead pkg ∧
                            (Cont completionRead (BHist.e0 hostTail) index -> False) ∧
                              (Cont completionRead (BHist.e1 hostTail) index -> False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet indexTailBudget budgetProvenanceShared sharedSealCompletion budgetPkg
    _sharedPkg completionPkg
  obtain ⟨indexUnary, _windowsUnary, _modulusUnary, _toleranceUnary, tailUnary,
    sealRowUnary, _transportsUnary, _routesUnary, provenanceUnary, _nameUnary,
    _indexWindowsModulus, _modulusToleranceTail, _tailSealRowTransports,
    _transportsRoutesProvenance, namePkg⟩ := packet
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed indexUnary tailUnary indexTailBudget
  have sharedUnary : UnaryHistory sharedTail :=
    unary_cont_closed budgetUnary provenanceUnary budgetProvenanceShared
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed sharedUnary sealRowUnary sharedSealCompletion
  have indexToCompletion : Cont index (append tail (append provenance sealRow)) completionRead := by
    cases indexTailBudget
    cases budgetProvenanceShared
    exact sharedSealCompletion.trans
      ((append_assoc (append index tail) provenance sealRow).trans
        (append_assoc index tail (append provenance sealRow)))
  exact
    ⟨budgetUnary, sharedUnary, completionUnary, indexTailBudget, budgetProvenanceShared,
      sharedSealCompletion, namePkg, completionPkg,
      (fun hostReturn =>
        cont_mutual_extension_right_tail_absurd.left indexToCompletion hostReturn),
      (fun hostReturn =>
        cont_mutual_extension_right_tail_absurd.right indexToCompletion hostReturn)⟩

end BEDC.Derived.UniformCauchyCriterionUp
