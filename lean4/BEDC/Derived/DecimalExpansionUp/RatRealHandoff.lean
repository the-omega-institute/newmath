import BEDC.Derived.DecimalExpansionUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.DecimalExpansionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DecimalExpansionRatRealHandoff [AskSetup] [PackageSetup]
    {D W V Q R E H C P N prefixRead comparison handoff sealRead endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory D →
      UnaryHistory W →
        UnaryHistory V →
          UnaryHistory Q →
            UnaryHistory R →
              UnaryHistory E →
                Cont D W prefixRead →
                  Cont prefixRead V comparison →
                    Cont comparison Q handoff →
                      Cont handoff R sealRead →
                        Cont sealRead E endpoint →
                          PkgSig bundle P pkg →
                            PkgSig bundle N pkg →
                              UnaryHistory prefixRead ∧ UnaryHistory comparison ∧
                                UnaryHistory handoff ∧ UnaryHistory sealRead ∧
                                  UnaryHistory endpoint ∧ Cont comparison Q handoff ∧
                                    Cont handoff R sealRead ∧ Cont sealRead E endpoint ∧
                                      PkgSig bundle P pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro dUnary wUnary vUnary qUnary rUnary eUnary digitWindow prefixPlace
    comparisonDyadic handoffRat sealEndpoint provenancePkg namePkg
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed dUnary wUnary digitWindow
  have comparisonUnary : UnaryHistory comparison :=
    unary_cont_closed prefixUnary vUnary prefixPlace
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed comparisonUnary qUnary comparisonDyadic
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed handoffUnary rUnary handoffRat
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed sealUnary eUnary sealEndpoint
  exact
    ⟨prefixUnary, comparisonUnary, handoffUnary, sealUnary, endpointUnary,
      comparisonDyadic, handoffRat, sealEndpoint, provenancePkg, namePkg⟩

end BEDC.Derived.DecimalExpansionUp
