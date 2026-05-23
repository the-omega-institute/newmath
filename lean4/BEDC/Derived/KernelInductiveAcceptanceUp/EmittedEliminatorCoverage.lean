import BEDC.Derived.KernelInductiveAcceptanceUp.TasteGate

namespace BEDC.Derived.KernelInductiveAcceptanceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem KernelInductiveAcceptanceUp_emitted_eliminator_consumer_coverage
    [AskSetup] [PackageSetup]
    {D S E P R H C Q N sigRead elimRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont D S sigRead ->
      Cont S E elimRead ->
        Cont elimRead R consumerRead ->
          PkgSig bundle Q pkg ->
            UnaryHistory D ->
              UnaryHistory S ->
                UnaryHistory E ->
                  UnaryHistory R ->
                    UnaryHistory consumerRead ∧ Cont D S sigRead ∧ Cont S E elimRead ∧
                      Cont elimRead R consumerRead ∧ PkgSig bundle Q pkg ∧
                        List.Mem (kernelInductiveAcceptanceEncodeBHist E)
                          (kernelInductiveAcceptanceToEventFlow
                            (KernelInductiveAcceptanceUp.mk D S E P R H C Q N)) := by
  -- BEDC touchpoint anchor: BHist BMark Cont ProbeBundle Pkg UnaryHistory
  intro declarationSignatures signaturesEliminators eliminatorConsumer packageRow
    declarationUnary signaturesUnary eliminatorsUnary recursionUnary
  have elimReadUnary : UnaryHistory elimRead :=
    unary_cont_closed signaturesUnary eliminatorsUnary signaturesEliminators
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed elimReadUnary recursionUnary eliminatorConsumer
  have eliminatorListed :
      List.Mem (kernelInductiveAcceptanceEncodeBHist E)
        (kernelInductiveAcceptanceToEventFlow
          (KernelInductiveAcceptanceUp.mk D S E P R H C Q N)) := by
    change
      List.Mem (kernelInductiveAcceptanceEncodeBHist E)
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
              (List.mem_cons_of_mem _ List.mem_cons_self))))
  exact
    ⟨consumerUnary, declarationSignatures, signaturesEliminators, eliminatorConsumer,
      packageRow, eliminatorListed⟩

end BEDC.Derived.KernelInductiveAcceptanceUp
