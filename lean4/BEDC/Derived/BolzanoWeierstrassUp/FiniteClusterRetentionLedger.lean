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

theorem BolzanoWeierstrassCarrier_finite_cluster_retention_ledger [AskSetup]
    [PackageSetup] {S K R Q E H C P N retainedCell selectedWindow readbackWindow
      clusterSeal : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg →
      Cont K R retainedCell →
        Cont retainedCell R selectedWindow →
          Cont selectedWindow Q readbackWindow →
            Cont readbackWindow E clusterSeal →
              PkgSig bundle clusterSeal pkg →
                SemanticNameCert
                    (fun row : BHist =>
                      hsame row clusterSeal ∧
                        BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg)
                    (fun row : BHist =>
                      hsame row retainedCell ∨ hsame row selectedWindow ∨
                        hsame row readbackWindow ∨ hsame row clusterSeal)
                    (fun row : BHist =>
                      hsame row clusterSeal ∧ Cont K R retainedCell ∧
                        Cont retainedCell R selectedWindow ∧
                          Cont selectedWindow Q readbackWindow ∧
                            Cont readbackWindow E clusterSeal ∧ PkgSig bundle P pkg ∧
                              PkgSig bundle clusterSeal pkg)
                    hsame ∧
                  UnaryHistory retainedCell ∧ UnaryHistory selectedWindow ∧
                    UnaryHistory readbackWindow ∧ UnaryHistory clusterSeal := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier retainedRoute selectedRoute readbackRoute clusterRoute clusterPkg
  have carrierWitness : BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg := carrier
  obtain ⟨_SUnary, KUnary, RUnary, QUnary, EUnary, _HUnary, _CUnary, _PUnary,
    _NUnary, _sourceIntervalRoute, _readbackSealRoute, _transportReplayRoute,
    carrierPkg⟩ := carrier
  have retainedUnary : UnaryHistory retainedCell :=
    unary_cont_closed KUnary RUnary retainedRoute
  have selectedUnary : UnaryHistory selectedWindow :=
    unary_cont_closed retainedUnary RUnary selectedRoute
  have readbackUnary : UnaryHistory readbackWindow :=
    unary_cont_closed selectedUnary QUnary readbackRoute
  have clusterUnary : UnaryHistory clusterSeal :=
    unary_cont_closed readbackUnary EUnary clusterRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row clusterSeal ∧
              BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg)
          (fun row : BHist =>
            hsame row retainedCell ∨ hsame row selectedWindow ∨ hsame row readbackWindow ∨
              hsame row clusterSeal)
          (fun row : BHist =>
            hsame row clusterSeal ∧ Cont K R retainedCell ∧
              Cont retainedCell R selectedWindow ∧ Cont selectedWindow Q readbackWindow ∧
                Cont readbackWindow E clusterSeal ∧ PkgSig bundle P pkg ∧
                  PkgSig bundle clusterSeal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro clusterSeal ⟨hsame_refl clusterSeal, carrierWitness⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr source.left))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.left, retainedRoute, selectedRoute, readbackRoute, clusterRoute, carrierPkg,
          clusterPkg⟩
  }
  exact ⟨cert, retainedUnary, selectedUnary, readbackUnary, clusterUnary⟩

end BEDC.Derived.BolzanoWeierstrassUp
