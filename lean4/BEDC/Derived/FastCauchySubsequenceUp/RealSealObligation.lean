import BEDC.Derived.FastCauchySubsequenceUp.NameCertObligations

namespace BEDC.Derived.FastCauchySubsequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FastCauchySubsequenceRealSealObligation [AskSetup] [PackageSetup]
    {S M Q F R W E H C P N modulusRead selectorRead fastRead regularRead
      realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastCauchySubsequenceCarrier S M Q F R W E H C P N bundle pkg →
      Cont S M modulusRead →
        Cont modulusRead Q selectorRead →
          Cont selectorRead F fastRead →
            Cont fastRead R regularRead →
              Cont regularRead E realRead →
                PkgSig bundle realRead pkg →
                  UnaryHistory modulusRead ∧ UnaryHistory selectorRead ∧
                    UnaryHistory fastRead ∧ UnaryHistory regularRead ∧
                      UnaryHistory realRead ∧ Cont S M modulusRead ∧
                        Cont modulusRead Q selectorRead ∧ Cont selectorRead F fastRead ∧
                          Cont fastRead R regularRead ∧ Cont regularRead E realRead ∧
                            PkgSig bundle P pkg ∧ PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: FastCauchySubsequenceCarrier BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier modulusRoute selectorRoute fastRoute regularRoute realRoute realPkg
  obtain ⟨unaryS, unaryM, unaryQ, unaryF, unaryR, _unaryW, unaryE, _unaryH, _unaryC,
    unaryP, _unaryN, provenancePkg, _localNamePkg⟩ := carrier
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed unaryS unaryM modulusRoute
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed modulusUnary unaryQ selectorRoute
  have fastUnary : UnaryHistory fastRead :=
    unary_cont_closed selectorUnary unaryF fastRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed fastUnary unaryR regularRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed regularUnary unaryE realRoute
  exact
    ⟨modulusUnary, selectorUnary, fastUnary, regularUnary, realUnary, modulusRoute,
      selectorRoute, fastRoute, regularRoute, realRoute, provenancePkg, realPkg⟩

end BEDC.Derived.FastCauchySubsequenceUp
