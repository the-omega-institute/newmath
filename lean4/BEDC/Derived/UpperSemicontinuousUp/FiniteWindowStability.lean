import BEDC.Derived.UpperSemicontinuousUp.TasteGate
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.UpperSemicontinuousUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UpperSemicontinuousFiniteWindowStability [AskSetup] [PackageSetup]
    {X F S W R O H C P N windowRead readbackRead comparisonRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory W ->
      UnaryHistory R ->
        UnaryHistory O ->
          UnaryHistory H ->
            UnaryHistory N ->
              Cont W R windowRead ->
                Cont windowRead O readbackRead ->
                  Cont readbackRead H comparisonRead ->
                    Cont comparisonRead N sealRead ->
                      PkgSig bundle sealRead pkg ->
                        UnaryHistory windowRead ∧ UnaryHistory readbackRead ∧
                          UnaryHistory comparisonRead ∧ UnaryHistory sealRead ∧
                            Cont W R windowRead ∧ Cont windowRead O readbackRead ∧
                              Cont readbackRead H comparisonRead ∧
                                Cont comparisonRead N sealRead ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro windowUnary readbackUnary comparisonUnary transportUnary localNameUnary windowRoute
    readbackRoute comparisonRoute sealRoute packageSeal
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed windowUnary readbackUnary windowRoute
  have readbackReadUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowReadUnary comparisonUnary readbackRoute
  have comparisonReadUnary : UnaryHistory comparisonRead :=
    unary_cont_closed readbackReadUnary transportUnary comparisonRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed comparisonReadUnary localNameUnary sealRoute
  exact
    ⟨windowReadUnary, readbackReadUnary, comparisonReadUnary, sealReadUnary, windowRoute,
      readbackRoute, comparisonRoute, sealRoute, packageSeal⟩

end BEDC.Derived.UpperSemicontinuousUp
