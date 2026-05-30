import BEDC.Derived.BolzanoWeierstrassUp.FiniteSubsequenceObligations
import BEDC.FKernel.NameCert

namespace BEDC.Derived.BolzanoWeierstrassUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BolzanoWeierstrassCarrier_cluster_seal_real_nonescape [AskSetup] [PackageSetup]
    {S K R Q E H C P N retainedWindow readbackWindow clusterSeal realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg →
      Cont K R retainedWindow →
        Cont retainedWindow Q readbackWindow →
          Cont readbackWindow E clusterSeal →
            Cont clusterSeal H realSeal →
              PkgSig bundle realSeal pkg →
                SemanticNameCert
                  (fun row : BHist =>
                    hsame row realSeal ∧
                      BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg)
                  (fun row : BHist =>
                    hsame row realSeal ∧ Cont K R retainedWindow ∧
                      Cont retainedWindow Q readbackWindow ∧
                        Cont readbackWindow E clusterSeal ∧ Cont clusterSeal H realSeal)
                  (fun row : BHist => hsame row realSeal ∧ PkgSig bundle realSeal pkg)
                  hsame ∧ UnaryHistory realSeal ∧ PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier retainedRoute readbackRoute clusterRoute realSealRoute realSealPkg
  have carrierSource :
      BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg :=
    carrier
  obtain ⟨_SUnary, KUnary, RUnary, QUnary, EUnary, HUnary, _CUnary, _PUnary,
    _NUnary, _sourceIntervalRoute, _readbackSealRoute, _transportReplayRoute,
    _carrierPkg⟩ := carrier
  have retainedUnary : UnaryHistory retainedWindow :=
    unary_cont_closed KUnary RUnary retainedRoute
  have readbackUnary : UnaryHistory readbackWindow :=
    unary_cont_closed retainedUnary QUnary readbackRoute
  have clusterUnary : UnaryHistory clusterSeal :=
    unary_cont_closed readbackUnary EUnary clusterRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed clusterUnary HUnary realSealRoute
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row realSeal ∧
            BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg)
        (fun row : BHist =>
          hsame row realSeal ∧ Cont K R retainedWindow ∧
            Cont retainedWindow Q readbackWindow ∧
              Cont readbackWindow E clusterSeal ∧ Cont clusterSeal H realSeal)
        (fun row : BHist => hsame row realSeal ∧ PkgSig bundle realSeal pkg)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro realSeal ⟨hsame_refl realSeal, carrierSource⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        exact
          ⟨hsame_trans (hsame_symm same) source.left, source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact
        ⟨source.left, retainedRoute, readbackRoute, clusterRoute, realSealRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, realSealPkg⟩
  }
  exact ⟨cert, realSealUnary, realSealPkg⟩

end BEDC.Derived.BolzanoWeierstrassUp
