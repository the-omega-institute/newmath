import BEDC.Derived.KernelInductiveAcceptanceUp.TasteGate

namespace BEDC.Derived.KernelInductiveAcceptanceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem KernelInductiveAcceptanceUp_positivity_refusal_classifier_stability
    [AskSetup] [PackageSetup]
    {declaration signatures eliminators positivity recursion transport routes provenance
      nameCert positivity' recursion' refusalRead refusalRead' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont positivity recursion refusalRead →
      hsame positivity positivity' →
        hsame recursion recursion' →
          Cont positivity' recursion' refusalRead' →
            PkgSig bundle refusalRead' pkg →
              UnaryHistory positivity →
                UnaryHistory recursion →
                  UnaryHistory refusalRead' ∧ hsame refusalRead refusalRead' ∧
                    Cont positivity' recursion' refusalRead' ∧
                      PkgSig bundle refusalRead' pkg ∧
                        List.Mem (kernelInductiveAcceptanceEncodeBHist positivity')
                          (kernelInductiveAcceptanceToEventFlow
                            (KernelInductiveAcceptanceUp.mk declaration signatures eliminators
                              positivity' recursion' transport routes provenance nameCert)) := by
  -- BEDC touchpoint anchor: BHist BMark Cont ProbeBundle Pkg hsame UnaryHistory
  intro positivityRecursionRefusal samePositivity sameRecursion positivityRecursionRefusal'
    refusalPkg positivityUnary recursionUnary
  have positivityUnary' : UnaryHistory positivity' :=
    unary_transport positivityUnary samePositivity
  have recursionUnary' : UnaryHistory recursion' :=
    unary_transport recursionUnary sameRecursion
  have refusalUnary' : UnaryHistory refusalRead' :=
    unary_cont_closed positivityUnary' recursionUnary' positivityRecursionRefusal'
  have refusalSame : hsame refusalRead refusalRead' :=
    cont_respects_hsame samePositivity sameRecursion positivityRecursionRefusal
      positivityRecursionRefusal'
  have positivityListed :
      List.Mem (kernelInductiveAcceptanceEncodeBHist positivity')
        (kernelInductiveAcceptanceToEventFlow
          (KernelInductiveAcceptanceUp.mk declaration signatures eliminators positivity'
            recursion' transport routes provenance nameCert)) := by
    change
      List.Mem (kernelInductiveAcceptanceEncodeBHist positivity')
        [[BMark.b0], kernelInductiveAcceptanceEncodeBHist declaration, [BMark.b1, BMark.b0],
          kernelInductiveAcceptanceEncodeBHist signatures, [BMark.b1, BMark.b1, BMark.b0],
          kernelInductiveAcceptanceEncodeBHist eliminators,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          kernelInductiveAcceptanceEncodeBHist positivity',
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          kernelInductiveAcceptanceEncodeBHist recursion',
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
              (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _
                  (List.mem_cons_of_mem _ List.mem_cons_self))))))
  exact
    ⟨refusalUnary', refusalSame, positivityRecursionRefusal', refusalPkg,
      positivityListed⟩

end BEDC.Derived.KernelInductiveAcceptanceUp
