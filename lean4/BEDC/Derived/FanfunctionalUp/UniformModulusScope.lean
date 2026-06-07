import BEDC.Derived.FanfunctionalUp.NameCertObligations

namespace BEDC.Derived.FanfunctionalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FanFunctionalUniformModulusScope [AskSetup] [PackageSetup]
    {C F eps B D W M H K P N prefixRead barRead witnessRead modulusRead
      namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FanFunctionalCarrierSurface C F eps B D W M H K P N bundle pkg ->
      Cont C F prefixRead ->
        Cont prefixRead B barRead ->
          Cont barRead W witnessRead ->
            Cont witnessRead M modulusRead ->
              Cont modulusRead N namedRead ->
                PkgSig bundle namedRead pkg ->
                  UnaryHistory C ∧ UnaryHistory F ∧ UnaryHistory B ∧
                    UnaryHistory W ∧ UnaryHistory M ∧ UnaryHistory prefixRead ∧
                      UnaryHistory barRead ∧ UnaryHistory witnessRead ∧
                        UnaryHistory modulusRead ∧ UnaryHistory namedRead ∧
                          Cont C F prefixRead ∧ Cont prefixRead B barRead ∧
                            Cont barRead W witnessRead ∧
                              Cont witnessRead M modulusRead ∧
                                Cont modulusRead N namedRead ∧ PkgSig bundle P pkg ∧
                                  PkgSig bundle namedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier prefixRoute barRoute witnessRoute modulusRoute namedRoute namedPkg
  obtain ⟨cUnary, fUnary, _epsUnary, bUnary, _dUnary, wUnary, mUnary, _hUnary,
    _kUnary, _pUnary, nUnary, _transportLocalName, _branchDepthWitness,
    _witnessModulusReplay, provenancePkg⟩ := carrier
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed cUnary fUnary prefixRoute
  have barUnary : UnaryHistory barRead :=
    unary_cont_closed prefixUnary bUnary barRoute
  have witnessUnary : UnaryHistory witnessRead :=
    unary_cont_closed barUnary wUnary witnessRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed witnessUnary mUnary modulusRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed modulusUnary nUnary namedRoute
  exact
    ⟨cUnary, fUnary, bUnary, wUnary, mUnary, prefixUnary, barUnary, witnessUnary,
      modulusUnary, namedUnary, prefixRoute, barRoute, witnessRoute, modulusRoute,
      namedRoute, provenancePkg, namedPkg⟩

end BEDC.Derived.FanfunctionalUp
