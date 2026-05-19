import BEDC.Derived.KernelInductiveAcceptanceUp.TasteGate

namespace BEDC.Derived.KernelInductiveAcceptanceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem KernelInductiveAcceptanceNontrivialBoundary [AskSetup] [PackageSetup]
    {declaration signatures eliminators positivity recursion transport routes provenance nameCert
      acceptedRead refusedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont declaration signatures acceptedRead →
      Cont signatures positivity refusedRead →
        PkgSig bundle acceptedRead pkg →
          PkgSig bundle refusedRead pkg →
            UnaryHistory declaration →
              UnaryHistory signatures →
                UnaryHistory positivity →
                  Exists fun packet : KernelInductiveAcceptanceUp =>
                    packet =
                        KernelInductiveAcceptanceUp.mk declaration signatures eliminators positivity
                          recursion transport routes provenance nameCert ∧
                      UnaryHistory acceptedRead ∧
                        UnaryHistory refusedRead ∧
                          Cont declaration signatures acceptedRead ∧
                            Cont signatures positivity refusedRead ∧
                              PkgSig bundle acceptedRead pkg ∧
                                PkgSig bundle refusedRead pkg ∧
                                  List.Mem (kernelInductiveAcceptanceEncodeBHist signatures)
                                    (kernelInductiveAcceptanceToEventFlow packet) ∧
                                    List.Mem (kernelInductiveAcceptanceEncodeBHist positivity)
                                      (kernelInductiveAcceptanceToEventFlow packet) := by
  -- BEDC touchpoint anchor: BHist BMark ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro declarationSignaturesRead signaturesPositivityRead acceptedPkg refusedPkg
    declarationUnary signaturesUnary positivityUnary
  let packet :=
    KernelInductiveAcceptanceUp.mk declaration signatures eliminators positivity recursion
      transport routes provenance nameCert
  have acceptedUnary : UnaryHistory acceptedRead :=
    unary_cont_closed declarationUnary signaturesUnary declarationSignaturesRead
  have refusedUnary : UnaryHistory refusedRead :=
    unary_cont_closed signaturesUnary positivityUnary signaturesPositivityRead
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
    ⟨packet,
      rfl,
      acceptedUnary,
      refusedUnary,
      declarationSignaturesRead,
      signaturesPositivityRead,
      acceptedPkg,
      refusedPkg,
      signaturesListed,
      positivityListed⟩

end BEDC.Derived.KernelInductiveAcceptanceUp
