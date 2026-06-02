import BEDC.Derived.BolzanoWeierstrassUp.FiniteSubsequenceObligations

namespace BEDC.Derived.BolzanoWeierstrassUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BolzanoWeierstrassCarrier_regseqrat_cluster_package [AskSetup] [PackageSetup]
    {S K R Q E H C P N sourceNet regseqWindow clusterSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg ->
      Cont S K sourceNet ->
        Cont sourceNet Q regseqWindow ->
          Cont regseqWindow E clusterSeal ->
            PkgSig bundle clusterSeal pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row clusterSeal ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row S ∨ hsame row K ∨ hsame row R ∨ hsame row Q ∨
                      hsame row E ∨ hsame row sourceNet ∨ hsame row regseqWindow ∨
                        hsame row clusterSeal)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont S K sourceNet ∧
                      Cont sourceNet Q regseqWindow ∧
                        Cont regseqWindow E clusterSeal ∧ PkgSig bundle P pkg ∧
                          PkgSig bundle clusterSeal pkg)
                  hsame ∧
                UnaryHistory sourceNet ∧ UnaryHistory regseqWindow ∧
                  UnaryHistory clusterSeal := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame UnaryHistory
  intro carrier sourceNetRoute regseqRoute clusterRoute clusterPkg
  obtain ⟨SUnary, KUnary, _RUnary, QUnary, EUnary, _HUnary, _CUnary, _PUnary,
    _NUnary, _sourceIntervalRoute, _readbackSealRoute, _transportReplayRoute,
    carrierPkg⟩ := carrier
  have sourceNetUnary : UnaryHistory sourceNet :=
    unary_cont_closed SUnary KUnary sourceNetRoute
  have regseqUnary : UnaryHistory regseqWindow :=
    unary_cont_closed sourceNetUnary QUnary regseqRoute
  have clusterUnary : UnaryHistory clusterSeal :=
    unary_cont_closed regseqUnary EUnary clusterRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row clusterSeal ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row K ∨ hsame row R ∨ hsame row Q ∨ hsame row E ∨
              hsame row sourceNet ∨ hsame row regseqWindow ∨ hsame row clusterSeal)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S K sourceNet ∧ Cont sourceNet Q regseqWindow ∧
              Cont regseqWindow E clusterSeal ∧ PkgSig bundle P pkg ∧
                PkgSig bundle clusterSeal pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro clusterSeal ⟨hsame_refl clusterSeal, clusterUnary⟩
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
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, sourceNetRoute, regseqRoute, clusterRoute, carrierPkg,
          clusterPkg⟩
  }
  exact ⟨cert, sourceNetUnary, regseqUnary, clusterUnary⟩

end BEDC.Derived.BolzanoWeierstrassUp
