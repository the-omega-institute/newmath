import BEDC.Derived.KernelInductiveAcceptanceUp.TasteGate

namespace BEDC.Derived.KernelInductiveAcceptanceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem KernelInductiveAcceptanceUp_environment_scope_route [AskSetup] [PackageSetup]
    {declaration signatures eliminators positivity recursion transport routes provenance nameCert
      environmentRead scopedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont declaration signatures environmentRead →
      Cont environmentRead routes scopedRead →
        PkgSig bundle scopedRead pkg →
          UnaryHistory declaration →
            UnaryHistory signatures →
              UnaryHistory routes →
                UnaryHistory environmentRead ∧ UnaryHistory scopedRead ∧
                  Cont declaration signatures environmentRead ∧
                    Cont environmentRead routes scopedRead ∧ PkgSig bundle scopedRead pkg ∧
                      List.Mem (kernelInductiveAcceptanceEncodeBHist declaration)
                        (kernelInductiveAcceptanceToEventFlow
                          (KernelInductiveAcceptanceUp.mk declaration signatures eliminators
                            positivity recursion transport routes provenance nameCert)) ∧
                        List.Mem (kernelInductiveAcceptanceEncodeBHist routes)
                          (kernelInductiveAcceptanceToEventFlow
                            (KernelInductiveAcceptanceUp.mk declaration signatures eliminators
                              positivity recursion transport routes provenance nameCert)) := by
  -- BEDC touchpoint anchor: BHist BMark Cont ProbeBundle PkgSig UnaryHistory
  intro declarationSignaturesEnvironment environmentRoutesScoped scopedPkg declarationUnary
    signaturesUnary routesUnary
  have environmentUnary : UnaryHistory environmentRead :=
    unary_cont_closed declarationUnary signaturesUnary declarationSignaturesEnvironment
  have scopedUnary : UnaryHistory scopedRead :=
    unary_cont_closed environmentUnary routesUnary environmentRoutesScoped
  have declarationListed :
      List.Mem (kernelInductiveAcceptanceEncodeBHist declaration)
        (kernelInductiveAcceptanceToEventFlow
          (KernelInductiveAcceptanceUp.mk declaration signatures eliminators positivity recursion
            transport routes provenance nameCert)) := by
    change
      List.Mem (kernelInductiveAcceptanceEncodeBHist declaration)
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
    exact List.mem_cons_of_mem _ List.mem_cons_self
  have routesListed :
      List.Mem (kernelInductiveAcceptanceEncodeBHist routes)
        (kernelInductiveAcceptanceToEventFlow
          (KernelInductiveAcceptanceUp.mk declaration signatures eliminators positivity recursion
            transport routes provenance nameCert)) := by
    change
      List.Mem (kernelInductiveAcceptanceEncodeBHist routes)
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
              (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _
                  (List.mem_cons_of_mem _
                    (List.mem_cons_of_mem _
                      (List.mem_cons_of_mem _
                        (List.mem_cons_of_mem _
                          (List.mem_cons_of_mem _
                            (List.mem_cons_of_mem _
                              (List.mem_cons_of_mem _ List.mem_cons_self))))))))))))
  exact
    ⟨environmentUnary, scopedUnary, declarationSignaturesEnvironment, environmentRoutesScoped,
      scopedPkg, declarationListed, routesListed⟩

end BEDC.Derived.KernelInductiveAcceptanceUp
