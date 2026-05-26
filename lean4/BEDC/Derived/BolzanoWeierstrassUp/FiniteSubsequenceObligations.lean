import BEDC.Derived.BolzanoWeierstrassUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BolzanoWeierstrassUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BolzanoWeierstrassCarrier [AskSetup] [PackageSetup]
    (S K R Q E H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory S ∧ UnaryHistory K ∧ UnaryHistory R ∧ UnaryHistory Q ∧
    UnaryHistory E ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
      UnaryHistory N ∧ Cont S K R ∧ Cont R Q E ∧ Cont H C P ∧ PkgSig bundle P pkg

theorem BolzanoWeierstrassCarrier_finite_subsequence_obligations [AskSetup] [PackageSetup]
    {S K R Q E H C P N subseqRead clusterRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg ->
      Cont K R subseqRead ->
        Cont subseqRead Q clusterRead ->
          PkgSig bundle clusterRead pkg ->
            UnaryHistory S ∧ UnaryHistory K ∧ UnaryHistory R ∧ UnaryHistory Q ∧
              UnaryHistory subseqRead ∧ UnaryHistory clusterRead ∧ Cont K R subseqRead ∧
                Cont subseqRead Q clusterRead ∧ PkgSig bundle P pkg ∧
                  PkgSig bundle clusterRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier subseqRoute clusterRoute clusterPkg
  obtain ⟨SUnary, KUnary, RUnary, QUnary, _EUnary, _HUnary, _CUnary, _PUnary,
    _NUnary, _sourceIntervalRoute, _readbackSealRoute, _transportReplayRoute,
    carrierPkg⟩ := carrier
  have subseqUnary : UnaryHistory subseqRead :=
    unary_cont_closed KUnary RUnary subseqRoute
  have clusterUnary : UnaryHistory clusterRead :=
    unary_cont_closed subseqUnary QUnary clusterRoute
  exact
    ⟨SUnary, KUnary, RUnary, QUnary, subseqUnary, clusterUnary, subseqRoute,
      clusterRoute, carrierPkg, clusterPkg⟩

end BEDC.Derived.BolzanoWeierstrassUp
