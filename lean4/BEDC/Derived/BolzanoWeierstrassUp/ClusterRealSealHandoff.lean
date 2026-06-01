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

theorem BolzanoWeierstrassCarrier_cluster_real_seal_handoff [AskSetup] [PackageSetup]
    {S K R Q E H C P N retainedWindow readbackWindow clusterSeal realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg ->
      Cont K R retainedWindow ->
        Cont retainedWindow Q readbackWindow ->
          Cont readbackWindow E clusterSeal ->
            Cont clusterSeal H realSeal ->
              PkgSig bundle realSeal pkg ->
                SemanticNameCert
                  (fun row : BHist =>
                    (hsame row retainedWindow ∨ hsame row readbackWindow ∨
                      hsame row clusterSeal ∨ hsame row realSeal) ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row K ∨ hsame row R ∨ hsame row Q ∨ hsame row E ∨
                      hsame row H ∨ hsame row retainedWindow ∨ hsame row readbackWindow ∨
                        hsame row clusterSeal ∨ hsame row realSeal)
                  (fun _row : BHist => PkgSig bundle P pkg ∧ PkgSig bundle realSeal pkg)
                  hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier retainedRoute readbackRoute clusterRoute realSealRoute realSealPkg
  obtain ⟨_SUnary, KUnary, RUnary, QUnary, EUnary, HUnary, _CUnary, _PUnary,
    _NUnary, _sourceIntervalRoute, _readbackSealRoute, _transportReplayRoute,
    carrierPkg⟩ := carrier
  have retainedUnary : UnaryHistory retainedWindow :=
    unary_cont_closed KUnary RUnary retainedRoute
  have readbackUnary : UnaryHistory readbackWindow :=
    unary_cont_closed retainedUnary QUnary readbackRoute
  have clusterUnary : UnaryHistory clusterSeal :=
    unary_cont_closed readbackUnary EUnary clusterRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed clusterUnary HUnary realSealRoute
  have sourceRealSeal :
      (fun row : BHist =>
        (hsame row retainedWindow ∨ hsame row readbackWindow ∨ hsame row clusterSeal ∨
          hsame row realSeal) ∧ UnaryHistory row) realSeal := by
    exact ⟨Or.inr (Or.inr (Or.inr (hsame_refl realSeal))), realSealUnary⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro realSeal sourceRealSeal
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
        have sourceRoute :
            hsame _other retainedWindow ∨ hsame _other readbackWindow ∨
              hsame _other clusterSeal ∨ hsame _other realSeal := by
          cases source.left with
          | inl retainedSame =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) retainedSame)
          | inr tail =>
              cases tail with
              | inl readbackSame =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) readbackSame))
              | inr tail' =>
                  cases tail' with
                  | inl clusterSame =>
                      exact Or.inr
                        (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) clusterSame)))
                  | inr realSame =>
                      exact Or.inr
                        (Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) realSame)))
        exact ⟨sourceRoute, unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl retainedSame =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl retainedSame)))))
      | inr tail =>
          cases tail with
          | inl readbackSame =>
              exact Or.inr
                (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl readbackSame))))))
          | inr tail' =>
              cases tail' with
              | inl clusterSame =>
                  exact Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl clusterSame)))))))
              | inr realSame =>
                  exact Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr realSame)))))))
    ledger_sound := by
      intro _row _source
      exact ⟨carrierPkg, realSealPkg⟩
  }

end BEDC.Derived.BolzanoWeierstrassUp
