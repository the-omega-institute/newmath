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

theorem BolzanoWeierstrassCarrier_finite_interval_subsequence_exhaustion
    [AskSetup] [PackageSetup]
    {S K R Q E H C P N retainedCell selectedWindow readbackWindow cauchyWindow
      clusterSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg ->
      Cont K R retainedCell ->
        Cont retainedCell R selectedWindow ->
          Cont selectedWindow Q readbackWindow ->
            Cont readbackWindow Q cauchyWindow ->
              Cont cauchyWindow E clusterSeal ->
                PkgSig bundle clusterSeal pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row clusterSeal ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row K ∨ hsame row R ∨ hsame row Q ∨
                          hsame row cauchyWindow ∨ Cont cauchyWindow E clusterSeal)
                      (fun row : BHist =>
                        PkgSig bundle P pkg ∧ PkgSig bundle clusterSeal pkg ∧
                          hsame row clusterSeal)
                      hsame ∧
                    UnaryHistory retainedCell ∧ UnaryHistory selectedWindow ∧
                      UnaryHistory readbackWindow ∧ UnaryHistory cauchyWindow ∧
                        UnaryHistory clusterSeal := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig SemanticNameCert hsame
  intro carrier retainedRoute selectedRoute readbackRoute cauchyRoute clusterRoute clusterPkg
  obtain ⟨_SUnary, KUnary, RUnary, QUnary, EUnary, _HUnary, _CUnary, _PUnary,
    _NUnary, _sourceIntervalRoute, _readbackSealRoute, _transportReplayRoute,
    carrierPkg⟩ := carrier
  have retainedUnary : UnaryHistory retainedCell :=
    unary_cont_closed KUnary RUnary retainedRoute
  have selectedUnary : UnaryHistory selectedWindow :=
    unary_cont_closed retainedUnary RUnary selectedRoute
  have readbackUnary : UnaryHistory readbackWindow :=
    unary_cont_closed selectedUnary QUnary readbackRoute
  have cauchyUnary : UnaryHistory cauchyWindow :=
    unary_cont_closed readbackUnary QUnary cauchyRoute
  have clusterUnary : UnaryHistory clusterSeal :=
    unary_cont_closed cauchyUnary EUnary clusterRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row clusterSeal ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row R ∨ hsame row Q ∨ hsame row cauchyWindow ∨
              Cont cauchyWindow E clusterSeal)
          (fun row : BHist =>
            PkgSig bundle P pkg ∧ PkgSig bundle clusterSeal pkg ∧ hsame row clusterSeal)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro clusterSeal ⟨hsame_refl clusterSeal, clusterUnary⟩
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row _source
      exact Or.inr (Or.inr (Or.inr (Or.inr clusterRoute)))
    ledger_sound := by
      intro _row source
      exact ⟨carrierPkg, clusterPkg, source.left⟩
  }
  exact
    ⟨cert, retainedUnary, selectedUnary, readbackUnary, cauchyUnary, clusterUnary⟩

end BEDC.Derived.BolzanoWeierstrassUp
