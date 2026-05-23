import BEDC.Derived.KernelInductiveAcceptanceUp.TasteGate

namespace BEDC.Derived.KernelInductiveAcceptanceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem KernelInductiveAcceptanceUp_subject_reduction_route [AskSetup] [PackageSetup]
    {declaration signatures eliminators positivity recursion transport routes provenance
      nameCert subjectRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory signatures ->
      UnaryHistory eliminators ->
        Cont signatures eliminators subjectRead ->
          PkgSig bundle subjectRead pkg ->
            UnaryHistory subjectRead ∧ Cont signatures eliminators subjectRead ∧
              PkgSig bundle subjectRead pkg ∧
                List.Mem (kernelInductiveAcceptanceEncodeBHist signatures)
                  (kernelInductiveAcceptanceToEventFlow
                    (KernelInductiveAcceptanceUp.mk declaration signatures eliminators
                      positivity recursion transport routes provenance nameCert)) ∧
                  List.Mem (kernelInductiveAcceptanceEncodeBHist eliminators)
                    (kernelInductiveAcceptanceToEventFlow
                      (KernelInductiveAcceptanceUp.mk declaration signatures eliminators
                        positivity recursion transport routes provenance nameCert)) ∧
                    List.Mem (kernelInductiveAcceptanceEncodeBHist recursion)
                      (kernelInductiveAcceptanceToEventFlow
                        (KernelInductiveAcceptanceUp.mk declaration signatures eliminators
                          positivity recursion transport routes provenance nameCert)) := by
  -- BEDC touchpoint anchor: BHist BMark Cont ProbeBundle Pkg UnaryHistory
  intro signaturesUnary eliminatorsUnary subjectCont subjectPkg
  have subjectUnary : UnaryHistory subjectRead :=
    unary_cont_closed signaturesUnary eliminatorsUnary subjectCont
  have signaturesListed :
      List.Mem (kernelInductiveAcceptanceEncodeBHist signatures)
        (kernelInductiveAcceptanceToEventFlow
          (KernelInductiveAcceptanceUp.mk declaration signatures eliminators positivity
            recursion transport routes provenance nameCert)) := by
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
  have recursionListed :
      List.Mem (kernelInductiveAcceptanceEncodeBHist recursion)
        (kernelInductiveAcceptanceToEventFlow
          (KernelInductiveAcceptanceUp.mk declaration signatures eliminators positivity
            recursion transport routes provenance nameCert)) := by
    change
      List.Mem (kernelInductiveAcceptanceEncodeBHist recursion)
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
                      (List.mem_cons_of_mem _ List.mem_cons_self))))))))
  exact
    ⟨subjectUnary, subjectCont, subjectPkg, signaturesListed, eliminatorsListed,
      recursionListed⟩

end BEDC.Derived.KernelInductiveAcceptanceUp
