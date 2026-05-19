import BEDC.Derived.KernelInductiveAcceptanceUp.TasteGate

namespace BEDC.Derived.KernelInductiveAcceptanceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem KernelInductiveAcceptanceObligationClosurePackage [AskSetup] [PackageSetup]
    {declaration signatures eliminators positivity recursion transport routes provenance
      nameCert signatureRead eliminatorRead refusalRead envRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont declaration signatures signatureRead →
      Cont signatures eliminators eliminatorRead →
        Cont positivity recursion refusalRead →
          Cont eliminators recursion envRead →
            PkgSig bundle envRead pkg →
              UnaryHistory declaration →
                UnaryHistory signatures →
                  UnaryHistory eliminators →
                    UnaryHistory positivity →
                      UnaryHistory recursion →
                        Exists fun packet : KernelInductiveAcceptanceUp =>
                          packet =
                              KernelInductiveAcceptanceUp.mk declaration signatures eliminators
                                positivity recursion transport routes provenance nameCert ∧
                            UnaryHistory signatureRead ∧ UnaryHistory eliminatorRead ∧
                              UnaryHistory refusalRead ∧ UnaryHistory envRead ∧
                                List.Mem (kernelInductiveAcceptanceEncodeBHist signatures)
                                  (kernelInductiveAcceptanceToEventFlow packet) ∧
                                  List.Mem (kernelInductiveAcceptanceEncodeBHist eliminators)
                                    (kernelInductiveAcceptanceToEventFlow packet) ∧
                                    List.Mem (kernelInductiveAcceptanceEncodeBHist positivity)
                                      (kernelInductiveAcceptanceToEventFlow packet) := by
  -- BEDC touchpoint anchor: BHist BMark Cont ProbeBundle Pkg UnaryHistory
  intro declarationSignaturesRead signaturesEliminatorsRead positivityRecursionRead
    eliminatorsRecursionRead _envPkg declarationUnary signaturesUnary eliminatorsUnary
    positivityUnary recursionUnary
  let packet :=
    KernelInductiveAcceptanceUp.mk declaration signatures eliminators positivity recursion
      transport routes provenance nameCert
  have signatureUnary : UnaryHistory signatureRead :=
    unary_cont_closed declarationUnary signaturesUnary declarationSignaturesRead
  have eliminatorUnary : UnaryHistory eliminatorRead :=
    unary_cont_closed signaturesUnary eliminatorsUnary signaturesEliminatorsRead
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed positivityUnary recursionUnary positivityRecursionRead
  have envUnary : UnaryHistory envRead :=
    unary_cont_closed eliminatorsUnary recursionUnary eliminatorsRecursionRead
  have signaturesListed :
      List.Mem (kernelInductiveAcceptanceEncodeBHist signatures)
        (kernelInductiveAcceptanceToEventFlow packet) := by
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
        (kernelInductiveAcceptanceToEventFlow packet) := by
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
        (kernelInductiveAcceptanceToEventFlow packet) := by
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
    ⟨packet, rfl, signatureUnary, eliminatorUnary, refusalUnary, envUnary,
      signaturesListed, eliminatorsListed, positivityListed⟩

end BEDC.Derived.KernelInductiveAcceptanceUp
