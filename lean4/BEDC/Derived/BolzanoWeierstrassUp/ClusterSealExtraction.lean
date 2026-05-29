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

theorem BolzanoWeierstrassCarrier_cluster_seal_extraction [AskSetup] [PackageSetup]
    {S K R Q E H C P N intervalTree retainedWindow readbackWindow clusterSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg →
      Cont S K intervalTree →
        Cont K R retainedWindow →
          Cont retainedWindow Q readbackWindow →
            Cont readbackWindow E clusterSeal →
              PkgSig bundle clusterSeal pkg →
                SemanticNameCert
                  (fun row : BHist =>
                    hsame row clusterSeal ∧
                      BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg)
                  (fun row : BHist =>
                    hsame row clusterSeal ∧ Cont S K intervalTree ∧
                      Cont K R retainedWindow ∧ Cont retainedWindow Q readbackWindow ∧
                        Cont readbackWindow E clusterSeal)
                  (fun row : BHist => hsame row clusterSeal ∧ PkgSig bundle clusterSeal pkg)
                  hsame ∧
                    UnaryHistory intervalTree ∧ UnaryHistory retainedWindow ∧
                      UnaryHistory readbackWindow ∧ UnaryHistory clusterSeal := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier intervalRoute retainedRoute readbackRoute clusterRoute clusterPkg
  have carrierSource :
      BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg :=
    carrier
  obtain ⟨SUnary, KUnary, RUnary, QUnary, EUnary, _HUnary, _CUnary, _PUnary,
    _NUnary, _sourceIntervalRoute, _readbackSealRoute, _transportReplayRoute,
    _carrierPkg⟩ := carrier
  have intervalUnary : UnaryHistory intervalTree :=
    unary_cont_closed SUnary KUnary intervalRoute
  have retainedUnary : UnaryHistory retainedWindow :=
    unary_cont_closed KUnary RUnary retainedRoute
  have readbackUnary : UnaryHistory readbackWindow :=
    unary_cont_closed retainedUnary QUnary readbackRoute
  have clusterUnary : UnaryHistory clusterSeal :=
    unary_cont_closed readbackUnary EUnary clusterRoute
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row clusterSeal ∧
            BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg)
        (fun row : BHist =>
          hsame row clusterSeal ∧ Cont S K intervalTree ∧
            Cont K R retainedWindow ∧ Cont retainedWindow Q readbackWindow ∧
              Cont readbackWindow E clusterSeal)
        (fun row : BHist => hsame row clusterSeal ∧ PkgSig bundle clusterSeal pkg)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro clusterSeal ⟨hsame_refl clusterSeal, carrierSource⟩
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
        ⟨source.left, intervalRoute, retainedRoute, readbackRoute, clusterRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, clusterPkg⟩
  }
  exact ⟨cert, intervalUnary, retainedUnary, readbackUnary, clusterUnary⟩

end BEDC.Derived.BolzanoWeierstrassUp
