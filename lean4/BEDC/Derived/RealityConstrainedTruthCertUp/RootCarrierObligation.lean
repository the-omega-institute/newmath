import BEDC.Derived.RealityConstrainedTruthCertUp

namespace BEDC.Derived.RealityConstrainedTruthCertUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealityConstrainedTruthCertRootCarrierObligation [AskSetup] [PackageSetup]
    {S Sigma K T U D I L F N failureRead openFitRead objectivityRead inductionRead towerRead
      exportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealityConstrainedTruthCertCarrier S Sigma K T U D I L F N →
      Cont F N failureRead →
        Cont S K openFitRead →
          Cont I L objectivityRead →
            Cont U D inductionRead →
              Cont T L towerRead →
                Cont failureRead N exportRead →
                  PkgSig bundle exportRead pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row exportRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row S ∨ hsame row Sigma ∨ hsame row K ∨ hsame row T ∨
                            hsame row U ∨ hsame row D ∨ hsame row I ∨ hsame row L ∨
                              hsame row F ∨ hsame row N ∨ hsame row exportRead)
                        (fun row : BHist =>
                          hsame row exportRead ∧ PkgSig bundle exportRead pkg)
                        hsame ∧
                      UnaryHistory openFitRead ∧
                        UnaryHistory objectivityRead ∧
                          UnaryHistory inductionRead ∧
                            UnaryHistory towerRead ∧ UnaryHistory exportRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier failureRoute openFitRoute objectivityRoute inductionRoute towerRoute exportRoute
    exportPkg
  obtain ⟨sourceUnary, signatureUnary, towerUnary, stabilityUnary, invariantUnary,
    ledgerUnary, sourceRoute, towerStabilityRoute, invariantRoute, nameRoute⟩ := carrier
  have classifierUnary : UnaryHistory K :=
    unary_cont_closed sourceUnary signatureUnary sourceRoute
  have descentUnary : UnaryHistory D :=
    unary_cont_closed towerUnary stabilityUnary towerStabilityRoute
  have failureUnary : UnaryHistory F :=
    unary_cont_closed invariantUnary ledgerUnary invariantRoute
  have nameUnary : UnaryHistory N :=
    unary_cont_closed ledgerUnary failureUnary nameRoute
  have failureReadUnary : UnaryHistory failureRead :=
    unary_cont_closed failureUnary nameUnary failureRoute
  have openFitReadUnary : UnaryHistory openFitRead :=
    unary_cont_closed sourceUnary classifierUnary openFitRoute
  have objectivityReadUnary : UnaryHistory objectivityRead :=
    unary_cont_closed invariantUnary ledgerUnary objectivityRoute
  have inductionReadUnary : UnaryHistory inductionRead :=
    unary_cont_closed stabilityUnary descentUnary inductionRoute
  have towerReadUnary : UnaryHistory towerRead :=
    unary_cont_closed towerUnary ledgerUnary towerRoute
  have exportReadUnary : UnaryHistory exportRead :=
    unary_cont_closed failureReadUnary nameUnary exportRoute
  have sourceExport :
      (fun row : BHist => hsame row exportRead ∧ UnaryHistory row) exportRead :=
    ⟨hsame_refl exportRead, exportReadUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row exportRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row S ∨ hsame row Sigma ∨ hsame row K ∨ hsame row T ∨
            hsame row U ∨ hsame row D ∨ hsame row I ∨ hsame row L ∨ hsame row F ∨
              hsame row N ∨ hsame row exportRead)
        (fun row : BHist => hsame row exportRead ∧ PkgSig bundle exportRead pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro exportRead sourceExport
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
        exact Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr source.left)))))))))
      ledger_sound := by
        intro _row source
        exact ⟨source.left, exportPkg⟩
    }
  exact
    ⟨cert, openFitReadUnary, objectivityReadUnary, inductionReadUnary, towerReadUnary,
      exportReadUnary⟩

end BEDC.Derived.RealityConstrainedTruthCertUp
