import BEDC.Derived.FastCauchySubsequenceUp.NameCertObligations

namespace BEDC.Derived.FastCauchySubsequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FastCauchySubsequenceCofinalSelectorStrictGrowth [AskSetup] [PackageSetup]
    {S M Q F R W E H C P N modulusRead selectorRead fastRead regularRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory M ->
      UnaryHistory Q ->
        UnaryHistory F ->
          UnaryHistory R ->
            Cont M Q selectorRead ->
              Cont selectorRead F fastRead ->
                Cont fastRead R regularRead ->
                  PkgSig bundle P pkg ->
                    PkgSig bundle regularRead pkg ->
                      UnaryHistory selectorRead ∧ UnaryHistory fastRead ∧
                        UnaryHistory regularRead ∧ Cont M Q selectorRead ∧
                          Cont selectorRead F fastRead ∧ Cont fastRead R regularRead ∧
                            PkgSig bundle P pkg ∧ PkgSig bundle regularRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig Cont UnaryHistory
  intro mUnary qUnary fUnary rUnary selectorRoute fastRoute regularRoute provenancePkg
    regularPkg
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed mUnary qUnary selectorRoute
  have fastUnary : UnaryHistory fastRead :=
    unary_cont_closed selectorUnary fUnary fastRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed fastUnary rUnary regularRoute
  exact
    ⟨selectorUnary, fastUnary, regularUnary, selectorRoute, fastRoute, regularRoute,
      provenancePkg, regularPkg⟩

end BEDC.Derived.FastCauchySubsequenceUp
