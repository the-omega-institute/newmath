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

theorem DecimalExpansionPrefixNormalizationTriad
    [AskSetup] [PackageSetup]
    {D W V Q R E H C P N prefixRead placeRead dyadicRead regseqRead realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory D ->
      UnaryHistory W ->
        UnaryHistory V ->
          UnaryHistory Q ->
            UnaryHistory R ->
              UnaryHistory E ->
                Cont D W prefixRead ->
                  Cont prefixRead V placeRead ->
                    Cont placeRead Q dyadicRead ->
                      Cont dyadicRead R regseqRead ->
                        Cont regseqRead E realSeal ->
                          PkgSig bundle P pkg ->
                            PkgSig bundle N pkg ->
                              UnaryHistory prefixRead ∧ UnaryHistory placeRead ∧
                                UnaryHistory dyadicRead ∧ UnaryHistory regseqRead ∧
                                  UnaryHistory realSeal ∧ Cont D W prefixRead ∧
                                    Cont prefixRead V placeRead ∧
                                      Cont placeRead Q dyadicRead ∧
                                        Cont dyadicRead R regseqRead ∧
                                          Cont regseqRead E realSeal ∧
                                            PkgSig bundle P pkg ∧
                                              PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro dUnary wUnary vUnary qUnary rUnary eUnary prefixRoute placeRoute
    dyadicRoute regseqRoute sealRoute provenancePkg namePkg
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed dUnary wUnary prefixRoute
  have placeUnary : UnaryHistory placeRead :=
    unary_cont_closed prefixUnary vUnary placeRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed placeUnary qUnary dyadicRoute
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed dyadicUnary rUnary regseqRoute
  have sealUnary : UnaryHistory realSeal :=
    unary_cont_closed regseqUnary eUnary sealRoute
  exact
    ⟨prefixUnary, placeUnary, dyadicUnary, regseqUnary, sealUnary, prefixRoute,
      placeRoute, dyadicRoute, regseqRoute, sealRoute, provenancePkg, namePkg⟩

end BEDC.Derived.DecimalExpansionUp
