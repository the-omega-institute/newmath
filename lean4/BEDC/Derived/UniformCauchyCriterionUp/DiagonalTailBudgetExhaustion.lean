import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_diagonal_tail_budget_exhaustion [AskSetup]
    [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name tailRead
      realRead tailBudgetRead hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index tail tailRead ->
        Cont tail sealRow realRead ->
          Cont tailRead realRead tailBudgetRead ->
            PkgSig bundle tailBudgetRead pkg ->
              UnaryHistory windows ∧ UnaryHistory tolerance ∧ UnaryHistory tailRead ∧
                UnaryHistory realRead ∧ UnaryHistory tailBudgetRead ∧
                  Cont index tail tailRead ∧ Cont tail sealRow realRead ∧
                    Cont tailRead realRead tailBudgetRead ∧ PkgSig bundle name pkg ∧
                      PkgSig bundle tailBudgetRead pkg ∧
                        (Cont tailBudgetRead (BHist.e0 hostTail) tailRead -> False) ∧
                          (Cont tailBudgetRead (BHist.e1 hostTail) tailRead -> False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet indexTailRead tailSealRealRead tailReadRealBudget budgetPkg
  obtain ⟨indexUnary, windowsUnary, _modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, _indexWindowsModulus,
    _modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed indexUnary tailUnary indexTailRead
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealRealRead
  have budgetUnary : UnaryHistory tailBudgetRead :=
    unary_cont_closed tailReadUnary realReadUnary tailReadRealBudget
  exact
    ⟨windowsUnary, toleranceUnary, tailReadUnary, realReadUnary, budgetUnary, indexTailRead,
      tailSealRealRead, tailReadRealBudget, namePkg, budgetPkg,
      (fun hostReturn =>
        cont_mutual_extension_right_tail_absurd.left tailReadRealBudget hostReturn),
      (fun hostReturn =>
        cont_mutual_extension_right_tail_absurd.right tailReadRealBudget hostReturn)⟩

end BEDC.Derived.UniformCauchyCriterionUp
