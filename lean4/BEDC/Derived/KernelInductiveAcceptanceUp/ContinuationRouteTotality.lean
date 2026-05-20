import BEDC.Derived.KernelInductiveAcceptanceUp.TasteGate

namespace BEDC.Derived.KernelInductiveAcceptanceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem KernelInductiveAcceptanceUp_cont_route_totality [AskSetup] [PackageSetup]
    {D S E P R H C Q N sigRead elimRead refuseRead envRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont D S sigRead ->
      Cont S E elimRead ->
        Cont P R refuseRead ->
          Cont E R envRead ->
            PkgSig bundle Q pkg ->
              UnaryHistory D ->
                UnaryHistory S ->
                  UnaryHistory E ->
                    UnaryHistory P ->
                      UnaryHistory R ->
                        UnaryHistory C ->
                          UnaryHistory sigRead ∧ UnaryHistory elimRead ∧
                            UnaryHistory refuseRead ∧ UnaryHistory envRead ∧
                              Cont D S sigRead ∧ Cont S E elimRead ∧
                                Cont P R refuseRead ∧ Cont E R envRead ∧
                                  PkgSig bundle Q pkg ∧
                                    List.Mem (kernelInductiveAcceptanceEncodeBHist C)
                                      (kernelInductiveAcceptanceToEventFlow
                                        (KernelInductiveAcceptanceUp.mk D S E P R H C Q N)) := by
  -- BEDC touchpoint anchor: BHist BMark Cont ProbeBundle Pkg UnaryHistory
  intro declarationSignaturesRead signaturesEliminatorsRead positivityRecursionRead
    eliminatorsRecursionRead packageSig declarationUnary signaturesUnary eliminatorsUnary
    positivityUnary recursionUnary _continuationUnary
  have sigUnary : UnaryHistory sigRead :=
    unary_cont_closed declarationUnary signaturesUnary declarationSignaturesRead
  have elimUnary : UnaryHistory elimRead :=
    unary_cont_closed signaturesUnary eliminatorsUnary signaturesEliminatorsRead
  have refuseUnary : UnaryHistory refuseRead :=
    unary_cont_closed positivityUnary recursionUnary positivityRecursionRead
  have envUnary : UnaryHistory envRead :=
    unary_cont_closed eliminatorsUnary recursionUnary eliminatorsRecursionRead
  have continuationListed :
      List.Mem (kernelInductiveAcceptanceEncodeBHist C)
        (kernelInductiveAcceptanceToEventFlow
          (KernelInductiveAcceptanceUp.mk D S E P R H C Q N)) := by
    change
      List.Mem (kernelInductiveAcceptanceEncodeBHist C)
        [[BMark.b0], kernelInductiveAcceptanceEncodeBHist D, [BMark.b1, BMark.b0],
          kernelInductiveAcceptanceEncodeBHist S, [BMark.b1, BMark.b1, BMark.b0],
          kernelInductiveAcceptanceEncodeBHist E,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          kernelInductiveAcceptanceEncodeBHist P,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          kernelInductiveAcceptanceEncodeBHist R,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          kernelInductiveAcceptanceEncodeBHist H,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          kernelInductiveAcceptanceEncodeBHist C,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b0],
          kernelInductiveAcceptanceEncodeBHist Q,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b0],
          kernelInductiveAcceptanceEncodeBHist N]
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
    ⟨sigUnary, elimUnary, refuseUnary, envUnary, declarationSignaturesRead,
      signaturesEliminatorsRead, positivityRecursionRead, eliminatorsRecursionRead,
      packageSig, continuationListed⟩

end BEDC.Derived.KernelInductiveAcceptanceUp
