import BEDC.Derived.ModulusContinuityUp.TasteGate

namespace BEDC.Derived.ModulusContinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ModulusContinuityCauchyRoute [AskSetup] [PackageSetup]
    {graph sourceWindow modulus dyadic readback realSeal _transport _replay _provenance _localName
      toleranceRead windowRead graphRead readbackRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory graph ->
      UnaryHistory sourceWindow ->
        UnaryHistory modulus ->
          UnaryHistory dyadic ->
            UnaryHistory readback ->
              UnaryHistory realSeal ->
                Cont dyadic modulus toleranceRead ->
                  Cont toleranceRead sourceWindow windowRead ->
                    Cont windowRead graph graphRead ->
                      Cont graphRead readback readbackRead ->
                        Cont readbackRead realSeal realRead ->
                          PkgSig bundle realRead pkg ->
                            UnaryHistory toleranceRead ∧ UnaryHistory windowRead ∧
                              UnaryHistory graphRead ∧ UnaryHistory readbackRead ∧
                                UnaryHistory realRead ∧ Cont dyadic modulus toleranceRead ∧
                                  Cont toleranceRead sourceWindow windowRead ∧
                                    Cont windowRead graph graphRead ∧
                                      Cont graphRead readback readbackRead ∧
                                        Cont readbackRead realSeal realRead ∧
                                          PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro graphUnary sourceWindowUnary modulusUnary dyadicUnary readbackUnary realSealUnary
    toleranceRoute windowRoute graphRoute readbackRoute realRoute realPkg
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed dyadicUnary modulusUnary toleranceRoute
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed toleranceReadUnary sourceWindowUnary windowRoute
  have graphReadUnary : UnaryHistory graphRead :=
    unary_cont_closed windowReadUnary graphUnary graphRoute
  have readbackReadUnary : UnaryHistory readbackRead :=
    unary_cont_closed graphReadUnary readbackUnary readbackRoute
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed readbackReadUnary realSealUnary realRoute
  exact
    ⟨toleranceReadUnary, windowReadUnary, graphReadUnary, readbackReadUnary, realReadUnary,
      toleranceRoute, windowRoute, graphRoute, readbackRoute, realRoute, realPkg⟩

end BEDC.Derived.ModulusContinuityUp
