import BEDC.Derived.MetaCICRedexFrontierUp.Nonescape

namespace BEDC.Derived.MetaCICRedexFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICRedexFrontierCarrier_normalization_window_handoff [AskSetup] [PackageSetup]
    {betaRedex appArgument lambdaDomain piDomain obstruction betaBoundary transport replay
      provenance nameCert betaRead obstructionRead boundaryRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont betaRedex betaBoundary betaRead →
      Cont obstruction betaBoundary obstructionRead →
        Cont betaRead transport boundaryRead →
          Cont obstructionRead replay replayRead →
            PkgSig bundle replayRead pkg →
              UnaryHistory betaRedex →
                UnaryHistory obstruction →
                  UnaryHistory betaBoundary →
                    UnaryHistory transport →
                      UnaryHistory replay →
                        UnaryHistory betaRead ∧ UnaryHistory obstructionRead ∧
                          UnaryHistory boundaryRead ∧ UnaryHistory replayRead ∧
                            PkgSig bundle replayRead pkg ∧
                              List.Mem (metaCICRedexFrontierEncodeBHist betaBoundary)
                                (metaCICRedexFrontierToEventFlow
                                  (MetaCICRedexFrontierUp.mk betaRedex appArgument
                                    lambdaDomain piDomain obstruction betaBoundary transport replay
                                    provenance nameCert)) ∧
                                List.Mem (metaCICRedexFrontierEncodeBHist obstruction)
                                  (metaCICRedexFrontierToEventFlow
                                    (MetaCICRedexFrontierUp.mk betaRedex appArgument
                                      lambdaDomain piDomain obstruction betaBoundary transport
                                      replay provenance nameCert)) := by
  -- BEDC touchpoint anchor: BHist BMark Cont ProbeBundle PkgSig UnaryHistory
  intro betaBoundaryRead obstructionBoundaryRead betaTransportRead obstructionReplayRead
    replayPkg betaUnary obstructionUnary boundaryUnary transportUnary replayUnary
  have betaReadUnary : UnaryHistory betaRead :=
    unary_cont_closed betaUnary boundaryUnary betaBoundaryRead
  have obstructionReadUnary : UnaryHistory obstructionRead :=
    unary_cont_closed obstructionUnary boundaryUnary obstructionBoundaryRead
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed betaReadUnary transportUnary betaTransportRead
  have replayReadUnary : UnaryHistory replayRead :=
    unary_cont_closed obstructionReadUnary replayUnary obstructionReplayRead
  have betaBoundaryListed :
      List.Mem (metaCICRedexFrontierEncodeBHist betaBoundary)
        (metaCICRedexFrontierToEventFlow
          (MetaCICRedexFrontierUp.mk betaRedex appArgument lambdaDomain piDomain obstruction
            betaBoundary transport replay provenance nameCert)) := by
    change
      List.Mem (metaCICRedexFrontierEncodeBHist betaBoundary)
        [[BMark.b0], metaCICRedexFrontierEncodeBHist betaRedex, [BMark.b1, BMark.b0],
          metaCICRedexFrontierEncodeBHist appArgument, [BMark.b1, BMark.b1, BMark.b0],
          metaCICRedexFrontierEncodeBHist lambdaDomain,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          metaCICRedexFrontierEncodeBHist piDomain,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          metaCICRedexFrontierEncodeBHist obstruction,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          metaCICRedexFrontierEncodeBHist betaBoundary,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          metaCICRedexFrontierEncodeBHist transport,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b0],
          metaCICRedexFrontierEncodeBHist replay,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b0],
          metaCICRedexFrontierEncodeBHist provenance,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b1, BMark.b0],
          metaCICRedexFrontierEncodeBHist nameCert]
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
  have obstructionListed :
      List.Mem (metaCICRedexFrontierEncodeBHist obstruction)
        (metaCICRedexFrontierToEventFlow
          (MetaCICRedexFrontierUp.mk betaRedex appArgument lambdaDomain piDomain obstruction
            betaBoundary transport replay provenance nameCert)) := by
    change
      List.Mem (metaCICRedexFrontierEncodeBHist obstruction)
        [[BMark.b0], metaCICRedexFrontierEncodeBHist betaRedex, [BMark.b1, BMark.b0],
          metaCICRedexFrontierEncodeBHist appArgument, [BMark.b1, BMark.b1, BMark.b0],
          metaCICRedexFrontierEncodeBHist lambdaDomain,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          metaCICRedexFrontierEncodeBHist piDomain,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          metaCICRedexFrontierEncodeBHist obstruction,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          metaCICRedexFrontierEncodeBHist betaBoundary,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          metaCICRedexFrontierEncodeBHist transport,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b0],
          metaCICRedexFrontierEncodeBHist replay,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b0],
          metaCICRedexFrontierEncodeBHist provenance,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b1, BMark.b0],
          metaCICRedexFrontierEncodeBHist nameCert]
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
    ⟨betaReadUnary, obstructionReadUnary, boundaryReadUnary, replayReadUnary, replayPkg,
      betaBoundaryListed, obstructionListed⟩

end BEDC.Derived.MetaCICRedexFrontierUp
