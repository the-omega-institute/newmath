import BEDC.Derived.MetaCICRedexFrontierUp.NameCertObligations

namespace BEDC.Derived.MetaCICRedexFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICRedexFrontierCarrier_obstruction_nonescape [AskSetup] [PackageSetup]
    {betaRedex appArgument lambdaDomain piDomain obstruction betaBoundary transport replay
      provenance nameCert obstructionRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont obstruction betaBoundary obstructionRead →
      Cont obstructionRead replay replayRead →
        PkgSig bundle replayRead pkg →
          UnaryHistory obstruction →
            UnaryHistory betaBoundary →
              UnaryHistory replay →
                UnaryHistory obstructionRead ∧ UnaryHistory replayRead ∧
                  Cont obstruction betaBoundary obstructionRead ∧
                    Cont obstructionRead replay replayRead ∧
                      PkgSig bundle replayRead pkg ∧
                        List.Mem (metaCICRedexFrontierEncodeBHist obstruction)
                          (metaCICRedexFrontierToEventFlow
                            (MetaCICRedexFrontierUp.mk betaRedex appArgument lambdaDomain
                              piDomain obstruction betaBoundary transport replay provenance
                              nameCert)) := by
  -- BEDC touchpoint anchor: BHist BMark Cont ProbeBundle PkgSig UnaryHistory
  intro obstructionBoundaryRead obstructionReplayRead replayPkg obstructionUnary boundaryUnary
    replayUnary
  have obstructionReadUnary : UnaryHistory obstructionRead :=
    unary_cont_closed obstructionUnary boundaryUnary obstructionBoundaryRead
  have replayReadUnary : UnaryHistory replayRead :=
    unary_cont_closed obstructionReadUnary replayUnary obstructionReplayRead
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
    ⟨obstructionReadUnary, replayReadUnary, obstructionBoundaryRead, obstructionReplayRead,
      replayPkg, obstructionListed⟩

end BEDC.Derived.MetaCICRedexFrontierUp
