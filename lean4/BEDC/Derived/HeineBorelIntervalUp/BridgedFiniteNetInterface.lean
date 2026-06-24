import BEDC.Derived.HeineBorelIntervalUp.ClusterFilterRoute

namespace BEDC.Derived.HeineBorelIntervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HeineBorelIntervalBridgedFiniteNetInterface [AskSetup] [PackageSetup]
    {A B K M Z F T S R E Q C P N net mesh coverageRead stableRead inductionRead sealRead
      publicRead clusterRead bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HeineBorelIntervalCoverageRoute
        (HeineBorelIntervalUp.mk A B K M Z F T S R E Q C P N)
        net mesh coverageRead bundle pkg →
      UnaryHistory T →
        UnaryHistory E →
          UnaryHistory N →
            UnaryHistory Q →
              UnaryHistory P →
                Cont coverageRead T stableRead →
                  HeineBorelIntervalFiniteNetInductionRoute
                      (HeineBorelIntervalUp.mk A B K M Z F T S R E Q C P N)
                      stableRead inductionRead bundle pkg →
                    Cont inductionRead E sealRead →
                      Cont sealRead N publicRead →
                        Cont publicRead Q clusterRead →
                          Cont clusterRead P bridgeRead →
                            PkgSig bundle stableRead pkg →
                              PkgSig bundle sealRead pkg →
                                PkgSig bundle publicRead pkg →
                                  PkgSig bundle clusterRead pkg →
                                    PkgSig bundle bridgeRead pkg →
                                      SemanticNameCert
                                          (fun row : BHist =>
                                            hsame row bridgeRead ∧ UnaryHistory row)
                                          (fun row : BHist =>
                                            hsame row coverageRead ∨ hsame row stableRead ∨
                                              hsame row inductionRead ∨ hsame row sealRead ∨
                                                hsame row publicRead ∨ hsame row clusterRead ∨
                                                  hsame row bridgeRead)
                                          (fun row : BHist =>
                                            UnaryHistory row ∧
                                              Cont coverageRead T stableRead ∧
                                                Cont inductionRead E sealRead ∧
                                                  Cont sealRead N publicRead ∧
                                                    Cont publicRead Q clusterRead ∧
                                                      Cont clusterRead P bridgeRead ∧
                                                        PkgSig bundle bridgeRead pkg)
                                          hsame ∧
                                        UnaryHistory bridgeRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro coverageRoute tailUnary eUnary nUnary qUnary pUnary coverageTailStable
    inductionRoute inductionSeal sealPublic publicCluster clusterBridge stablePkg sealPkg
    publicPkg clusterPkg bridgePkg
  have clusterResult :
      SemanticNameCert
          (fun row : BHist => hsame row clusterRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row coverageRead ∨ hsame row stableRead ∨ hsame row inductionRead ∨
              hsame row sealRead ∨ hsame row publicRead ∨ hsame row clusterRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont coverageRead T stableRead ∧
              Cont inductionRead E sealRead ∧ Cont sealRead N publicRead ∧
                Cont publicRead Q clusterRead ∧ PkgSig bundle clusterRead pkg)
          hsame ∧
        UnaryHistory clusterRead :=
    HeineBorelIntervalClusterFilterRoute
      coverageRoute tailUnary eUnary nUnary qUnary coverageTailStable inductionRoute
      inductionSeal sealPublic publicCluster stablePkg sealPkg publicPkg clusterPkg
  have clusterUnary : UnaryHistory clusterRead := clusterResult.right
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed clusterUnary pUnary clusterBridge
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row coverageRead ∨ hsame row stableRead ∨ hsame row inductionRead ∨
              hsame row sealRead ∨ hsame row publicRead ∨ hsame row clusterRead ∨
                hsame row bridgeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont coverageRead T stableRead ∧
              Cont inductionRead E sealRead ∧ Cont sealRead N publicRead ∧
                Cont publicRead Q clusterRead ∧ Cont clusterRead P bridgeRead ∧
                  PkgSig bundle bridgeRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro bridgeRead ⟨hsame_refl bridgeRead, bridgeUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, coverageTailStable, inductionSeal, sealPublic, publicCluster,
          clusterBridge, bridgePkg⟩
  }
  exact ⟨cert, bridgeUnary⟩

end BEDC.Derived.HeineBorelIntervalUp
