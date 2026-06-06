import BEDC.Derived.FastCauchySubsequenceUp.NameCertObligations

namespace BEDC.Derived.FastCauchySubsequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FastCauchySubsequenceRegularReadback [AskSetup] [PackageSetup]
    {S M Q F R W E H C P N selectorRead fastRead regularRead rationalRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastCauchySubsequenceCarrier S M Q F R W E H C P N bundle pkg ->
      Cont M Q selectorRead ->
        Cont selectorRead F fastRead ->
          Cont fastRead R regularRead ->
            Cont regularRead W rationalRead ->
              Cont rationalRead E sealRead ->
                PkgSig bundle sealRead pkg ->
                  UnaryHistory selectorRead ∧ UnaryHistory fastRead ∧
                    UnaryHistory regularRead ∧ UnaryHistory rationalRead ∧
                      UnaryHistory sealRead ∧ Cont M Q selectorRead ∧
                        Cont selectorRead F fastRead ∧ Cont fastRead R regularRead ∧
                          Cont regularRead W rationalRead ∧ Cont rationalRead E sealRead ∧
                            PkgSig bundle P pkg ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: FastCauchySubsequenceCarrier BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier selectorRoute fastRoute regularRoute rationalRoute sealRoute sealPkg
  obtain ⟨_unaryS, unaryM, unaryQ, unaryF, unaryR, unaryW, unaryE, _unaryH,
    _unaryC, _unaryP, _unaryN, carrierProvenancePkg, _localNamePkg⟩ := carrier
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed unaryM unaryQ selectorRoute
  have fastUnary : UnaryHistory fastRead :=
    unary_cont_closed selectorUnary unaryF fastRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed fastUnary unaryR regularRoute
  have rationalUnary : UnaryHistory rationalRead :=
    unary_cont_closed regularUnary unaryW rationalRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed rationalUnary unaryE sealRoute
  exact
    ⟨selectorUnary, fastUnary, regularUnary, rationalUnary, sealUnary, selectorRoute,
      fastRoute, regularRoute, rationalRoute, sealRoute, carrierProvenancePkg, sealPkg⟩

end BEDC.Derived.FastCauchySubsequenceUp
