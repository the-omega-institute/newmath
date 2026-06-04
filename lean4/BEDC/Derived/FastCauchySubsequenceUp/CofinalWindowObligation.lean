import BEDC.Derived.FastCauchySubsequenceUp.NameCertObligations

namespace BEDC.Derived.FastCauchySubsequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FastCauchySubsequenceCofinalWindowObligation [AskSetup] [PackageSetup]
    {S M Q F R W E H C P N modulusRead selectorRead cofinalWindow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastCauchySubsequenceCarrier S M Q F R W E H C P N bundle pkg ->
      Cont S M modulusRead ->
        Cont modulusRead Q selectorRead ->
          Cont selectorRead W cofinalWindow ->
            PkgSig bundle cofinalWindow pkg ->
              UnaryHistory modulusRead ∧ UnaryHistory selectorRead ∧
                UnaryHistory cofinalWindow ∧ Cont S M modulusRead ∧
                  Cont modulusRead Q selectorRead ∧ Cont selectorRead W cofinalWindow ∧
                    PkgSig bundle P pkg ∧ PkgSig bundle cofinalWindow pkg := by
  -- BEDC touchpoint anchor: FastCauchySubsequenceCarrier BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier modulusRoute selectorRoute cofinalRoute cofinalPkg
  obtain ⟨unaryS, unaryM, unaryQ, _unaryF, _unaryR, unaryW, _unaryE, _unaryH,
    _unaryC, _unaryP, _unaryN, provenancePkg, _localNamePkg⟩ := carrier
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed unaryS unaryM modulusRoute
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed modulusUnary unaryQ selectorRoute
  have cofinalUnary : UnaryHistory cofinalWindow :=
    unary_cont_closed selectorUnary unaryW cofinalRoute
  exact
    ⟨modulusUnary, selectorUnary, cofinalUnary, modulusRoute, selectorRoute,
      cofinalRoute, provenancePkg, cofinalPkg⟩

end BEDC.Derived.FastCauchySubsequenceUp
