import BEDC.Derived.BaireCategoryUp.NameCertObligations
import BEDC.FKernel.Cont

namespace BEDC.Derived.BaireCategoryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BaireCategoryCarrier_mature_consumer_completeness [AskSetup] [PackageSetup]
    {B M D O R T H C P N compactRead meagreRead denseRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireCategoryCarrier B M D O R T H C P N bundle pkg →
      Cont B M denseRead →
        Cont denseRead T realRead →
          Cont D O compactRead →
            Cont R T meagreRead →
              PkgSig bundle realRead pkg →
                UnaryHistory denseRead ∧ UnaryHistory realRead ∧ UnaryHistory compactRead ∧
                  UnaryHistory meagreRead ∧ PkgSig bundle P pkg ∧
                    PkgSig bundle realRead pkg ∧
                      baireCategoryFields (BaireCategoryUp.mk B M D O R T H C P N) =
                        [B, M, D, O, R, T, H, C, P, N] := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier denseRoute realRoute compactRoute meagreRoute realPkg
  obtain ⟨bUnary, mUnary, dUnary, oUnary, rUnary, tUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, provenancePkg⟩ := carrier
  have denseUnary : UnaryHistory denseRead :=
    unary_cont_closed bUnary mUnary denseRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed denseUnary tUnary realRoute
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed dUnary oUnary compactRoute
  have meagreUnary : UnaryHistory meagreRead :=
    unary_cont_closed rUnary tUnary meagreRoute
  exact
    ⟨denseUnary, realUnary, compactUnary, meagreUnary, provenancePkg, realPkg, rfl⟩

end BEDC.Derived.BaireCategoryUp
