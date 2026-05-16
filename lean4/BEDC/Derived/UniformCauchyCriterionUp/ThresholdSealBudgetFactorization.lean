import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_threshold_seal_budget_factorization [AskSetup]
    [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name thresholdRead
      tailRead sealRead sealBudgetRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index windows thresholdRead ->
        Cont index tail tailRead ->
          Cont tail sealRow sealRead ->
            Cont tailRead sealRead sealBudgetRead ->
              Cont sealBudgetRead provenance consumerRead ->
                PkgSig bundle thresholdRead pkg ->
                  PkgSig bundle tailRead pkg ->
                    PkgSig bundle sealRead pkg ->
                      PkgSig bundle sealBudgetRead pkg ->
                        PkgSig bundle consumerRead pkg ->
                          UnaryHistory thresholdRead ∧ UnaryHistory tailRead ∧
                            UnaryHistory sealRead ∧ UnaryHistory sealBudgetRead ∧
                              UnaryHistory consumerRead ∧ hsame modulus thresholdRead ∧
                                Cont index windows thresholdRead ∧ Cont index tail tailRead ∧
                                  Cont tail sealRow sealRead ∧
                                    Cont tailRead sealRead sealBudgetRead ∧
                                      Cont sealBudgetRead provenance consumerRead ∧
                                        PkgSig bundle name pkg ∧
                                          PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet indexWindowsThreshold indexTailRead tailSealRead tailSealBudget
    sealBudgetConsumer _thresholdPkg _tailPkg _sealPkg _sealBudgetPkg consumerPkg
  obtain ⟨indexUnary, windowsUnary, modulusUnary, _toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, provenanceUnary, _nameUnary, indexWindowsModulus,
    _modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have thresholdUnary : UnaryHistory thresholdRead :=
    unary_cont_closed indexUnary windowsUnary indexWindowsThreshold
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed indexUnary tailUnary indexTailRead
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealRead
  have sealBudgetUnary : UnaryHistory sealBudgetRead :=
    unary_cont_closed tailReadUnary sealReadUnary tailSealBudget
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed sealBudgetUnary provenanceUnary sealBudgetConsumer
  have sameThreshold : hsame modulus thresholdRead :=
    cont_respects_hsame (hsame_refl index) (hsame_refl windows) indexWindowsModulus
      indexWindowsThreshold
  exact
    ⟨thresholdUnary, tailReadUnary, sealReadUnary, sealBudgetUnary, consumerUnary,
      sameThreshold, indexWindowsThreshold, indexTailRead, tailSealRead, tailSealBudget,
      sealBudgetConsumer, namePkg, consumerPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
