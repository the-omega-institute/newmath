import BEDC.Derived.FastCauchySubsequenceUp.NameCertObligations

namespace BEDC.Derived.FastCauchySubsequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FastCauchySubsequenceCofinalTailObligation [AskSetup] [PackageSetup]
    {S M Q F R W E H C P N modulusRead selectorRead tailWindow fastRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastCauchySubsequenceCarrier S M Q F R W E H C P N bundle pkg ->
      Cont S M modulusRead ->
        Cont modulusRead Q selectorRead ->
          Cont selectorRead W tailWindow ->
            Cont tailWindow F fastRead ->
              PkgSig bundle fastRead pkg ->
                UnaryHistory modulusRead ∧ UnaryHistory selectorRead ∧
                  UnaryHistory tailWindow ∧ UnaryHistory fastRead ∧
                    Cont modulusRead Q selectorRead ∧ Cont selectorRead W tailWindow ∧
                      Cont tailWindow F fastRead ∧ PkgSig bundle P pkg ∧
                        PkgSig bundle fastRead pkg := by
  -- BEDC touchpoint anchor: FastCauchySubsequenceCarrier BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier modulusRoute selectorRoute tailRoute fastRoute fastPkg
  obtain ⟨unaryS, unaryM, unaryQ, unaryF, _unaryR, unaryW, _unaryE, _unaryH,
    _unaryC, _unaryP, _unaryN, provenancePkg, _localNamePkg⟩ := carrier
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed unaryS unaryM modulusRoute
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed modulusUnary unaryQ selectorRoute
  have tailUnary : UnaryHistory tailWindow :=
    unary_cont_closed selectorUnary unaryW tailRoute
  have fastUnary : UnaryHistory fastRead :=
    unary_cont_closed tailUnary unaryF fastRoute
  exact
    ⟨modulusUnary, selectorUnary, tailUnary, fastUnary, selectorRoute, tailRoute,
      fastRoute, provenancePkg, fastPkg⟩

end BEDC.Derived.FastCauchySubsequenceUp
