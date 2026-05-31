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

theorem BolzanoWeierstrassCarrier_choice_free_cluster_package [AskSetup] [PackageSetup]
    {S K R Q E H C P N depthCell retainedCell tailCell regRead clusterSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg →
      Cont S K depthCell →
        Cont depthCell K retainedCell →
          Cont retainedCell R tailCell →
            Cont tailCell Q regRead →
              Cont regRead E clusterSeal →
                PkgSig bundle clusterSeal pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row clusterSeal ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row S ∨ hsame row K ∨ hsame row R ∨ hsame row Q ∨
                          hsame row E ∨ hsame row clusterSeal)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont S K depthCell ∧
                          Cont depthCell K retainedCell ∧ Cont retainedCell R tailCell ∧
                            Cont tailCell Q regRead ∧ Cont regRead E clusterSeal ∧
                              PkgSig bundle P pkg ∧ PkgSig bundle clusterSeal pkg)
                      hsame ∧
                    UnaryHistory clusterSeal := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier depthRoute retainedRoute tailRoute regRoute clusterRoute clusterPkg
  obtain ⟨SUnary, KUnary, RUnary, QUnary, EUnary, _HUnary, _CUnary, _PUnary,
    _NUnary, _sourceIntervalRoute, _readbackSealRoute, _transportReplayRoute,
    carrierPkg⟩ := carrier
  have depthUnary : UnaryHistory depthCell :=
    unary_cont_closed SUnary KUnary depthRoute
  have retainedUnary : UnaryHistory retainedCell :=
    unary_cont_closed depthUnary KUnary retainedRoute
  have tailUnary : UnaryHistory tailCell :=
    unary_cont_closed retainedUnary RUnary tailRoute
  have regUnary : UnaryHistory regRead :=
    unary_cont_closed tailUnary QUnary regRoute
  have clusterUnary : UnaryHistory clusterSeal :=
    unary_cont_closed regUnary EUnary clusterRoute
  have sourceCluster :
      (fun row : BHist => hsame row clusterSeal ∧ UnaryHistory row) clusterSeal := by
    exact ⟨hsame_refl clusterSeal, clusterUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row clusterSeal ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row K ∨ hsame row R ∨ hsame row Q ∨
              hsame row E ∨ hsame row clusterSeal)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S K depthCell ∧ Cont depthCell K retainedCell ∧
              Cont retainedCell R tailCell ∧ Cont tailCell Q regRead ∧
                Cont regRead E clusterSeal ∧ PkgSig bundle P pkg ∧
                  PkgSig bundle clusterSeal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro clusterSeal sourceCluster
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, depthRoute, retainedRoute, tailRoute, regRoute, clusterRoute,
          carrierPkg, clusterPkg⟩
  }
  exact ⟨cert, clusterUnary⟩

end BEDC.Derived.BolzanoWeierstrassUp
