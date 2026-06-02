import BEDC.Derived.BolzanoWeierstrassUp.FiniteSubsequenceObligations

namespace BEDC.Derived.BolzanoWeierstrassUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BolzanoWeierstrassCarrier_dyadic_mesh_subsequence_witness [AskSetup] [PackageSetup]
    {S K R Q E H C P N depthCell boundedWindow nextIndex dyadicWitness : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg ->
      Cont K S depthCell ->
        Cont depthCell R boundedWindow ->
          Cont boundedWindow Q nextIndex ->
            Cont nextIndex E dyadicWitness ->
              PkgSig bundle dyadicWitness pkg ->
                UnaryHistory depthCell ∧ UnaryHistory boundedWindow ∧
                  UnaryHistory nextIndex ∧ UnaryHistory dyadicWitness ∧
                    Cont K S depthCell ∧ Cont depthCell R boundedWindow ∧
                      Cont boundedWindow Q nextIndex ∧ Cont nextIndex E dyadicWitness ∧
                        PkgSig bundle P pkg ∧ PkgSig bundle dyadicWitness pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier depthRoute windowRoute indexRoute witnessRoute witnessPkg
  obtain ⟨SUnary, KUnary, RUnary, QUnary, EUnary, _HUnary, _CUnary, _PUnary,
    _NUnary, _sourceIntervalRoute, _readbackSealRoute, _transportReplayRoute,
    carrierPkg⟩ := carrier
  have depthUnary : UnaryHistory depthCell :=
    unary_cont_closed KUnary SUnary depthRoute
  have windowUnary : UnaryHistory boundedWindow :=
    unary_cont_closed depthUnary RUnary windowRoute
  have indexUnary : UnaryHistory nextIndex :=
    unary_cont_closed windowUnary QUnary indexRoute
  have witnessUnary : UnaryHistory dyadicWitness :=
    unary_cont_closed indexUnary EUnary witnessRoute
  exact
    ⟨depthUnary, windowUnary, indexUnary, witnessUnary, depthRoute, windowRoute,
      indexRoute, witnessRoute, carrierPkg, witnessPkg⟩

end BEDC.Derived.BolzanoWeierstrassUp
