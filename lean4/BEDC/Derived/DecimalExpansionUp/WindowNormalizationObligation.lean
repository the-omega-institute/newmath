import BEDC.Derived.DecimalExpansionUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Package

namespace BEDC.Derived.DecimalExpansionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DecimalExpansionWindowNormalizationObligation
    [AskSetup] [PackageSetup]
    {D W V Q R E H C P N prefixRead comparison handoff sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory D →
      UnaryHistory W →
        UnaryHistory V →
          UnaryHistory Q →
            UnaryHistory R →
              Cont D W prefixRead →
                Cont prefixRead V comparison →
                  Cont comparison Q handoff →
                    Cont handoff R sealRead →
                      PkgSig bundle P pkg →
                        PkgSig bundle N pkg →
                          UnaryHistory prefixRead ∧ UnaryHistory comparison ∧
                            UnaryHistory handoff ∧ UnaryHistory sealRead ∧
                              Cont D W prefixRead ∧ Cont prefixRead V comparison ∧
                                Cont comparison Q handoff ∧ Cont handoff R sealRead ∧
                                  PkgSig bundle P pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro dUnary wUnary vUnary qUnary rUnary prefixRoute comparisonRoute handoffRoute
    sealRoute provenancePkg namePkg
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed dUnary wUnary prefixRoute
  have comparisonUnary : UnaryHistory comparison :=
    unary_cont_closed prefixUnary vUnary comparisonRoute
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed comparisonUnary qUnary handoffRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed handoffUnary rUnary sealRoute
  exact
    ⟨prefixUnary, comparisonUnary, handoffUnary, sealUnary, prefixRoute,
      comparisonRoute, handoffRoute, sealRoute, provenancePkg, namePkg⟩

end BEDC.Derived.DecimalExpansionUp
