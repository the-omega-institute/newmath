import BEDC.Derived.FastCauchySubsequenceUp.NameCertObligations

namespace BEDC.Derived.FastCauchySubsequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FastCauchySubsequenceTailRegularity [AskSetup] [PackageSetup]
    {S M Q F R W E H C P N modulusRead selectorRead fastRead regularRead tailRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastCauchySubsequenceCarrier S M Q F R W E H C P N bundle pkg ->
      Cont S M modulusRead ->
        Cont modulusRead Q selectorRead ->
          Cont selectorRead F fastRead ->
            Cont fastRead R regularRead ->
              Cont regularRead W tailRead ->
                PkgSig bundle tailRead pkg ->
                  UnaryHistory tailRead ∧ Cont fastRead R regularRead ∧
                    Cont regularRead W tailRead ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle N pkg ∧ PkgSig bundle tailRead pkg := by
  -- BEDC touchpoint anchor: FastCauchySubsequenceCarrier BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier modulusRoute selectorRoute fastRoute regularRoute tailRoute tailPkg
  obtain ⟨sUnary, mUnary, qUnary, fUnary, rUnary, wUnary, _eUnary, _hUnary,
    _cUnary, _pUnary, _nUnary, provenancePkg, localNamePkg⟩ := carrier
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed sUnary mUnary modulusRoute
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed modulusUnary qUnary selectorRoute
  have fastUnary : UnaryHistory fastRead :=
    unary_cont_closed selectorUnary fUnary fastRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed fastUnary rUnary regularRoute
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed regularUnary wUnary tailRoute
  exact ⟨tailUnary, regularRoute, tailRoute, provenancePkg, localNamePkg, tailPkg⟩

end BEDC.Derived.FastCauchySubsequenceUp
