import BEDC.Derived.KernelInductiveAcceptanceUp.TasteGate

namespace BEDC.Derived.KernelInductiveAcceptanceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.FKernel.Mark

theorem KernelInductiveAcceptanceUp_environment_entry_determinacy
    [AskSetup] [PackageSetup]
    {declaration signatures eliminators positivity recursion transport routes provenance
      nameCert entry entry' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont declaration signatures eliminators →
      Cont eliminators recursion entry →
        Cont eliminators recursion entry' →
          PkgSig bundle entry pkg →
            PkgSig bundle entry' pkg →
              UnaryHistory declaration →
                UnaryHistory signatures →
                  UnaryHistory eliminators →
                    UnaryHistory recursion →
                      hsame entry entry' ∧ UnaryHistory entry ∧ UnaryHistory entry' ∧
                        List.Mem (kernelInductiveAcceptanceEncodeBHist eliminators)
                          (kernelInductiveAcceptanceToEventFlow
                            (KernelInductiveAcceptanceUp.mk declaration signatures eliminators
                              positivity recursion transport routes provenance nameCert)) := by
  -- BEDC touchpoint anchor: BHist BMark Cont ProbeBundle Pkg
  intro _declarationSignaturesEliminators eliminatorsRecursionEntry
    eliminatorsRecursionEntry' _entryPkg _entryPkg' _declarationUnary _signaturesUnary
    eliminatorsUnary recursionUnary
  have sameEntry : hsame entry entry' :=
    cont_deterministic eliminatorsRecursionEntry eliminatorsRecursionEntry'
  have entryUnary : UnaryHistory entry :=
    unary_cont_closed eliminatorsUnary recursionUnary eliminatorsRecursionEntry
  have entryUnary' : UnaryHistory entry' :=
    unary_cont_closed eliminatorsUnary recursionUnary eliminatorsRecursionEntry'
  have eliminatorsListed :
      List.Mem (kernelInductiveAcceptanceEncodeBHist eliminators)
        (kernelInductiveAcceptanceToEventFlow
          (KernelInductiveAcceptanceUp.mk declaration signatures eliminators positivity
            recursion transport routes provenance nameCert)) := by
    change
      List.Mem (kernelInductiveAcceptanceEncodeBHist eliminators)
        [[BMark.b0], kernelInductiveAcceptanceEncodeBHist declaration, [BMark.b1, BMark.b0],
          kernelInductiveAcceptanceEncodeBHist signatures, [BMark.b1, BMark.b1, BMark.b0],
          kernelInductiveAcceptanceEncodeBHist eliminators,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          kernelInductiveAcceptanceEncodeBHist positivity,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          kernelInductiveAcceptanceEncodeBHist recursion,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          kernelInductiveAcceptanceEncodeBHist transport,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          kernelInductiveAcceptanceEncodeBHist routes,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b0],
          kernelInductiveAcceptanceEncodeBHist provenance,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b0],
          kernelInductiveAcceptanceEncodeBHist nameCert]
    exact
      List.mem_cons_of_mem _
        (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ List.mem_cons_self))))
  exact ⟨sameEntry, entryUnary, entryUnary', eliminatorsListed⟩

end BEDC.Derived.KernelInductiveAcceptanceUp
