import BEDC.Derived.MetaCICRedexFrontierUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MetaCICRedexFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICRedexFrontierCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {betaRedex appArgument lambdaDomain piDomain obstruction betaBoundary transport replay
      provenance nameCert betaRead appRead lambdaRead piRead boundaryRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont betaRedex betaBoundary betaRead →
      Cont appArgument betaBoundary appRead →
        Cont lambdaDomain betaBoundary lambdaRead →
          Cont piDomain betaBoundary piRead →
            Cont betaRead transport boundaryRead →
              Cont boundaryRead replay replayRead →
                PkgSig bundle replayRead pkg →
                  UnaryHistory betaRedex →
                    UnaryHistory appArgument →
                      UnaryHistory lambdaDomain →
                        UnaryHistory piDomain →
                          UnaryHistory betaBoundary →
                            UnaryHistory transport →
                              UnaryHistory replay →
                                UnaryHistory betaRead ∧ UnaryHistory appRead ∧
                                  UnaryHistory lambdaRead ∧ UnaryHistory piRead ∧
                                    UnaryHistory boundaryRead ∧ UnaryHistory replayRead ∧
                                      PkgSig bundle replayRead pkg ∧
                                        List.Mem
                                          (metaCICRedexFrontierEncodeBHist betaRedex)
                                          (metaCICRedexFrontierToEventFlow
                                            (MetaCICRedexFrontierUp.mk betaRedex appArgument
                                              lambdaDomain piDomain obstruction betaBoundary
                                              transport replay provenance nameCert)) := by
  -- BEDC touchpoint anchor: BHist BMark Cont ProbeBundle PkgSig UnaryHistory
  intro betaBoundaryRead appBoundaryRead lambdaBoundaryRead piBoundaryRead betaTransportRead
    boundaryReplayRead replayPkg betaUnary appUnary lambdaUnary piUnary boundaryUnary
    transportUnary replayUnary
  have betaReadUnary : UnaryHistory betaRead :=
    unary_cont_closed betaUnary boundaryUnary betaBoundaryRead
  have appReadUnary : UnaryHistory appRead :=
    unary_cont_closed appUnary boundaryUnary appBoundaryRead
  have lambdaReadUnary : UnaryHistory lambdaRead :=
    unary_cont_closed lambdaUnary boundaryUnary lambdaBoundaryRead
  have piReadUnary : UnaryHistory piRead :=
    unary_cont_closed piUnary boundaryUnary piBoundaryRead
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed betaReadUnary transportUnary betaTransportRead
  have replayReadUnary : UnaryHistory replayRead :=
    unary_cont_closed boundaryReadUnary replayUnary boundaryReplayRead
  have betaListed :
      List.Mem (metaCICRedexFrontierEncodeBHist betaRedex)
        (metaCICRedexFrontierToEventFlow
          (MetaCICRedexFrontierUp.mk betaRedex appArgument lambdaDomain piDomain obstruction
            betaBoundary transport replay provenance nameCert)) := by
    change
      List.Mem (metaCICRedexFrontierEncodeBHist betaRedex)
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
    exact List.mem_cons_of_mem _ List.mem_cons_self
  exact
    ⟨betaReadUnary, appReadUnary, lambdaReadUnary, piReadUnary, boundaryReadUnary,
      replayReadUnary, replayPkg, betaListed⟩

end BEDC.Derived.MetaCICRedexFrontierUp
