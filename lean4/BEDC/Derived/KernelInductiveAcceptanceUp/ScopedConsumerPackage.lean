import BEDC.Derived.KernelInductiveAcceptanceUp.TasteGate

namespace BEDC.Derived.KernelInductiveAcceptanceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem KernelInductiveAcceptanceUp_scoped_consumer_package [AskSetup] [PackageSetup]
    {declaration signatures eliminators positivity recursion transport routes provenance
      nameCert signatureRead eliminatorRead refusalRead subjectRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont declaration signatures signatureRead ->
      Cont signatures eliminators eliminatorRead ->
        Cont positivity recursion refusalRead ->
          Cont eliminators recursion subjectRead ->
            PkgSig bundle subjectRead pkg ->
              UnaryHistory declaration ->
                UnaryHistory signatures ->
                  UnaryHistory eliminators ->
                    UnaryHistory positivity ->
                      UnaryHistory recursion ->
                        UnaryHistory signatureRead ∧ UnaryHistory eliminatorRead ∧
                          UnaryHistory refusalRead ∧ UnaryHistory subjectRead ∧
                            Cont declaration signatures signatureRead ∧
                              Cont signatures eliminators eliminatorRead ∧
                                Cont positivity recursion refusalRead ∧
                                  Cont eliminators recursion subjectRead ∧
                                    PkgSig bundle subjectRead pkg ∧
                                      List.Mem
                                        (kernelInductiveAcceptanceEncodeBHist signatures)
                                        (kernelInductiveAcceptanceToEventFlow
                                          (KernelInductiveAcceptanceUp.mk declaration
                                            signatures eliminators positivity recursion
                                            transport routes provenance nameCert)) ∧
                                        List.Mem
                                          (kernelInductiveAcceptanceEncodeBHist eliminators)
                                          (kernelInductiveAcceptanceToEventFlow
                                            (KernelInductiveAcceptanceUp.mk declaration
                                              signatures eliminators positivity recursion
                                              transport routes provenance nameCert)) ∧
                                          List.Mem
                                            (kernelInductiveAcceptanceEncodeBHist positivity)
                                            (kernelInductiveAcceptanceToEventFlow
                                              (KernelInductiveAcceptanceUp.mk declaration
                                                signatures eliminators positivity recursion
                                                transport routes provenance nameCert)) := by
  -- BEDC touchpoint anchor: BHist BMark Cont ProbeBundle Pkg UnaryHistory
  intro declarationSignaturesRead signaturesEliminatorsRead positivityRecursionRead
    eliminatorsRecursionRead subjectPkg declarationUnary signaturesUnary eliminatorsUnary
    positivityUnary recursionUnary
  have signatureUnary : UnaryHistory signatureRead :=
    unary_cont_closed declarationUnary signaturesUnary declarationSignaturesRead
  have eliminatorUnary : UnaryHistory eliminatorRead :=
    unary_cont_closed signaturesUnary eliminatorsUnary signaturesEliminatorsRead
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed positivityUnary recursionUnary positivityRecursionRead
  have subjectUnary : UnaryHistory subjectRead :=
    unary_cont_closed eliminatorsUnary recursionUnary eliminatorsRecursionRead
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
  have positivityListed :
      List.Mem (kernelInductiveAcceptanceEncodeBHist positivity)
        (kernelInductiveAcceptanceToEventFlow
          (KernelInductiveAcceptanceUp.mk declaration signatures eliminators positivity
            recursion transport routes provenance nameCert)) := by
    change
      List.Mem (kernelInductiveAcceptanceEncodeBHist positivity)
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
                  (List.mem_cons_of_mem _ List.mem_cons_self))))))
  exact
    ⟨signatureUnary, eliminatorUnary, refusalUnary, subjectUnary, declarationSignaturesRead,
      signaturesEliminatorsRead, positivityRecursionRead, eliminatorsRecursionRead,
      subjectPkg, signaturesListed, eliminatorsListed, positivityListed⟩

end BEDC.Derived.KernelInductiveAcceptanceUp
