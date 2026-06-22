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

theorem MetaCICRedexFrontierCandidateSNWindow [AskSetup] [PackageSetup]
    {B A L P O E H C G N betaRead appRead lambdaRead piRead normalizationRead
      handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICRedexFrontierCarrier B A L P O E H C G N →
      Cont B E betaRead →
        Cont A E appRead →
          Cont L E lambdaRead →
            Cont P E piRead →
              Cont betaRead O normalizationRead →
                Cont normalizationRead C handoffRead →
                  PkgSig bundle handoffRead pkg →
                    UnaryHistory betaRead ∧ UnaryHistory appRead ∧
                      UnaryHistory lambdaRead ∧ UnaryHistory piRead ∧
                        UnaryHistory normalizationRead ∧ UnaryHistory handoffRead ∧
                          hsame H (append B O) ∧ Cont betaRead O normalizationRead ∧
                            Cont normalizationRead C handoffRead ∧
                              PkgSig bundle handoffRead pkg := by
  -- BEDC touchpoint anchor: MetaCICRedexFrontierCarrier BHist Cont ProbeBundle PkgSig
  intro carrier betaRoute appRoute lambdaRoute piRoute normalizationRoute handoffRoute
    handoffPkg
  obtain ⟨bUnary, aUnary, lUnary, pUnary, oUnary, eUnary, _gUnary, boundarySame,
    _carrierBetaRoute, _carrierArgRoute, _carrierProvenanceRoute⟩ := carrier
  have betaUnary : UnaryHistory betaRead :=
    unary_cont_closed bUnary eUnary betaRoute
  have appUnary : UnaryHistory appRead :=
    unary_cont_closed aUnary eUnary appRoute
  have lambdaUnary : UnaryHistory lambdaRead :=
    unary_cont_closed lUnary eUnary lambdaRoute
  have piUnary : UnaryHistory piRead :=
    unary_cont_closed pUnary eUnary piRoute
  have normalizationUnary : UnaryHistory normalizationRead :=
    unary_cont_closed betaUnary oUnary normalizationRoute
  have cUnary : UnaryHistory C :=
    unary_cont_closed bUnary eUnary _carrierBetaRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed normalizationUnary cUnary handoffRoute
  exact
    ⟨betaUnary, appUnary, lambdaUnary, piUnary, normalizationUnary, handoffUnary,
      boundarySame, normalizationRoute, handoffRoute, handoffPkg⟩

end BEDC.Derived.MetaCICRedexFrontierUp
