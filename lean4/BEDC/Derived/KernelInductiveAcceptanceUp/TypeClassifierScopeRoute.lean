import BEDC.Derived.KernelInductiveAcceptanceUp.TasteGate

namespace BEDC.Derived.KernelInductiveAcceptanceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem KernelInductiveAcceptanceUp_typeclassifier_scope_route [AskSetup] [PackageSetup]
    {declaration signatures eliminators positivity recursion transport routes provenance nameCert
      classifierRead scopedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont signatures transport classifierRead →
      Cont classifierRead routes scopedRead →
        PkgSig bundle scopedRead pkg →
          UnaryHistory signatures →
            UnaryHistory transport →
              UnaryHistory routes →
                UnaryHistory classifierRead ∧ UnaryHistory scopedRead ∧
                  Cont signatures transport classifierRead ∧
                    Cont classifierRead routes scopedRead ∧ PkgSig bundle scopedRead pkg ∧
                      List.Mem (kernelInductiveAcceptanceEncodeBHist signatures)
                        (kernelInductiveAcceptanceToEventFlow
                          (KernelInductiveAcceptanceUp.mk declaration signatures eliminators
                            positivity recursion transport routes provenance nameCert)) ∧
                        List.Mem (kernelInductiveAcceptanceEncodeBHist transport)
                          (kernelInductiveAcceptanceToEventFlow
                            (KernelInductiveAcceptanceUp.mk declaration signatures eliminators
                              positivity recursion transport routes provenance nameCert)) := by
  -- BEDC touchpoint anchor: BHist BMark Cont ProbeBundle PkgSig UnaryHistory
  intro signaturesTransportRead classifierRoutesRead scopedPkg signaturesUnary transportUnary
    routesUnary
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed signaturesUnary transportUnary signaturesTransportRead
  have scopedUnary : UnaryHistory scopedRead :=
    unary_cont_closed classifierUnary routesUnary classifierRoutesRead
  have signaturesListed :
      List.Mem (kernelInductiveAcceptanceEncodeBHist signatures)
        (kernelInductiveAcceptanceToEventFlow
          (KernelInductiveAcceptanceUp.mk declaration signatures eliminators positivity recursion
            transport routes provenance nameCert)) := by
    change
      List.Mem (kernelInductiveAcceptanceEncodeBHist signatures)
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
          (List.mem_cons_of_mem _ List.mem_cons_self))
  have transportListed :
      List.Mem (kernelInductiveAcceptanceEncodeBHist transport)
        (kernelInductiveAcceptanceToEventFlow
          (KernelInductiveAcceptanceUp.mk declaration signatures eliminators positivity recursion
            transport routes provenance nameCert)) := by
    change
      List.Mem (kernelInductiveAcceptanceEncodeBHist transport)
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
                          (List.mem_cons_of_mem _ List.mem_cons_self))))))))))
  exact
    ⟨classifierUnary, scopedUnary, signaturesTransportRead, classifierRoutesRead, scopedPkg,
      signaturesListed, transportListed⟩

end BEDC.Derived.KernelInductiveAcceptanceUp
