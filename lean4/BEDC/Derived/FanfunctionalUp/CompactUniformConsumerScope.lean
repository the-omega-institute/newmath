import BEDC.Derived.FanfunctionalUp.NameCertObligations

namespace BEDC.Derived.FanfunctionalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FanFunctionalCompactUniformConsumerScope [AskSetup] [PackageSetup]
    {C F eps B D W M H K P N prefixRead depthRead witnessRead modulusRead named : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FanFunctionalCarrierSurface C F eps B D W M H K P N bundle pkg ->
      Cont C B prefixRead ->
        Cont F D depthRead ->
          Cont prefixRead W witnessRead ->
            Cont witnessRead M modulusRead ->
              Cont modulusRead N named ->
                PkgSig bundle named pkg ->
                  UnaryHistory C ∧ UnaryHistory F ∧ UnaryHistory B ∧ UnaryHistory D ∧
                    UnaryHistory W ∧ UnaryHistory M ∧ UnaryHistory prefixRead ∧
                      UnaryHistory depthRead ∧ UnaryHistory witnessRead ∧
                        UnaryHistory modulusRead ∧ UnaryHistory named ∧
                          Cont C B prefixRead ∧ Cont F D depthRead ∧
                            Cont prefixRead W witnessRead ∧
                              Cont witnessRead M modulusRead ∧ Cont modulusRead N named ∧
                                PkgSig bundle named pkg := by
  -- BEDC touchpoint anchor: FanFunctionalCarrierSurface BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier prefixRoute depthRoute witnessRoute modulusRoute namedRoute namedPkg
  obtain ⟨cUnary, fUnary, _epsUnary, bUnary, dUnary, wUnary, mUnary, _hUnary, _kUnary,
    _pUnary, nUnary, _transportLocalName, _carrierBranchDepthWitness,
    _carrierWitnessModulusReplay, _carrierProvenancePkg⟩ := carrier
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed cUnary bUnary prefixRoute
  have depthUnary : UnaryHistory depthRead :=
    unary_cont_closed fUnary dUnary depthRoute
  have witnessUnary : UnaryHistory witnessRead :=
    unary_cont_closed prefixUnary wUnary witnessRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed witnessUnary mUnary modulusRoute
  have namedUnary : UnaryHistory named :=
    unary_cont_closed modulusUnary nUnary namedRoute
  exact
    ⟨cUnary, fUnary, bUnary, dUnary, wUnary, mUnary, prefixUnary, depthUnary,
      witnessUnary, modulusUnary, namedUnary, prefixRoute, depthRoute, witnessRoute,
      modulusRoute, namedRoute, namedPkg⟩

end BEDC.Derived.FanfunctionalUp
