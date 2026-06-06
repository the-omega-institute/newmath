import BEDC.Derived.FastCauchySubsequenceUp.NameCertObligations

namespace BEDC.Derived.FastCauchySubsequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FastCauchySubsequenceRealSealHandoff [AskSetup] [PackageSetup]
    {S M Q F R W E H C P N modulusRead selectorRead fastRead regularRead readbackRead
      realRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastCauchySubsequenceCarrier S M Q F R W E H C P N bundle pkg ->
      Cont S M modulusRead ->
        Cont modulusRead Q selectorRead ->
          Cont selectorRead F fastRead ->
            Cont fastRead R regularRead ->
              Cont regularRead W readbackRead ->
                Cont readbackRead E realRead ->
                  Cont realRead N namedRead ->
                    PkgSig bundle namedRead pkg ->
                      UnaryHistory modulusRead ∧ UnaryHistory selectorRead ∧
                        UnaryHistory fastRead ∧ UnaryHistory regularRead ∧
                          UnaryHistory readbackRead ∧ UnaryHistory realRead ∧
                            UnaryHistory namedRead ∧ Cont S M modulusRead ∧
                              Cont modulusRead Q selectorRead ∧
                                Cont selectorRead F fastRead ∧
                                  Cont fastRead R regularRead ∧
                                    Cont regularRead W readbackRead ∧
                                      Cont readbackRead E realRead ∧
                                        Cont realRead N namedRead ∧
                                          PkgSig bundle P pkg ∧
                                            PkgSig bundle namedRead pkg := by
  -- BEDC touchpoint anchor: FastCauchySubsequenceCarrier BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier modulusRoute selectorRoute fastRoute regularRoute readbackRoute realRoute
    namedRoute namedPkg
  obtain ⟨unaryS, unaryM, unaryQ, unaryF, unaryR, unaryW, unaryE, _unaryH, _unaryC,
    unaryP, unaryN, provenancePkg, _localNamePkg⟩ := carrier
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed unaryS unaryM modulusRoute
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed modulusUnary unaryQ selectorRoute
  have fastUnary : UnaryHistory fastRead :=
    unary_cont_closed selectorUnary unaryF fastRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed fastUnary unaryR regularRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed regularUnary unaryW readbackRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed readbackUnary unaryE realRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed realUnary unaryN namedRoute
  exact
    ⟨modulusUnary, selectorUnary, fastUnary, regularUnary, readbackUnary, realUnary,
      namedUnary, modulusRoute, selectorRoute, fastRoute, regularRoute, readbackRoute,
      realRoute, namedRoute, provenancePkg, namedPkg⟩

end BEDC.Derived.FastCauchySubsequenceUp
