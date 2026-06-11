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
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICRedexFrontierCandidateNormalization [AskSetup] [PackageSetup]
    {betaRedex appArgument lambdaDomain piDomain obstruction betaBoundary transport replay
      provenance name betaRead appRead lambdaRead piRead normalizationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont betaRedex betaBoundary betaRead →
      Cont appArgument betaBoundary appRead →
        Cont lambdaDomain betaBoundary lambdaRead →
          Cont piDomain betaBoundary piRead →
            Cont betaRead obstruction normalizationRead →
              PkgSig bundle normalizationRead pkg →
                UnaryHistory betaRedex →
                  UnaryHistory appArgument →
                    UnaryHistory lambdaDomain →
                      UnaryHistory piDomain →
                        UnaryHistory obstruction →
                          UnaryHistory betaBoundary →
                            UnaryHistory betaRead ∧ UnaryHistory appRead ∧
                              UnaryHistory lambdaRead ∧ UnaryHistory piRead ∧
                                UnaryHistory normalizationRead ∧
                                  Cont betaRead obstruction normalizationRead ∧
                                    PkgSig bundle normalizationRead pkg ∧
                                      metaCICRedexFrontierFromEventFlow
                                          (metaCICRedexFrontierToEventFlow
                                            (MetaCICRedexFrontierUp.mk betaRedex
                                              appArgument lambdaDomain piDomain obstruction
                                              betaBoundary transport replay provenance name)) =
                                        some
                                          (MetaCICRedexFrontierUp.mk betaRedex appArgument
                                            lambdaDomain piDomain obstruction betaBoundary
                                            transport replay provenance name) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro betaRoute appRoute lambdaRoute piRoute normalizationRoute normalizationPkg betaUnary
    appUnary lambdaUnary piUnary obstructionUnary boundaryUnary
  have betaReadUnary : UnaryHistory betaRead :=
    unary_cont_closed betaUnary boundaryUnary betaRoute
  have appReadUnary : UnaryHistory appRead :=
    unary_cont_closed appUnary boundaryUnary appRoute
  have lambdaReadUnary : UnaryHistory lambdaRead :=
    unary_cont_closed lambdaUnary boundaryUnary lambdaRoute
  have piReadUnary : UnaryHistory piRead :=
    unary_cont_closed piUnary boundaryUnary piRoute
  have normalizationUnary : UnaryHistory normalizationRead :=
    unary_cont_closed betaReadUnary obstructionUnary normalizationRoute
  exact
    ⟨betaReadUnary, appReadUnary, lambdaReadUnary, piReadUnary, normalizationUnary,
      normalizationRoute, normalizationPkg,
      metaCICRedexFrontierChapterTasteGate.round_trip
        (MetaCICRedexFrontierUp.mk betaRedex appArgument lambdaDomain piDomain obstruction
          betaBoundary transport replay provenance name)⟩

end BEDC.Derived.MetaCICRedexFrontierUp
