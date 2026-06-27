import BEDC.Derived.CauchyDifferenceCriterionUp.ScopePackage

namespace BEDC.Derived.CauchyDifferenceCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyDifferenceCriterionScopedKernelBinding [AskSetup] [PackageSetup]
    {X Y D Z Q W T E H C P N diffRead nullRead sealRead scopeRead exportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory X →
      UnaryHistory Y →
        UnaryHistory D →
          UnaryHistory Z →
            UnaryHistory Q →
              UnaryHistory W →
                UnaryHistory T →
                  UnaryHistory E →
                    UnaryHistory N →
                      Cont D Z diffRead →
                        Cont diffRead Q nullRead →
                          Cont nullRead E sealRead →
                            Cont sealRead W scopeRead →
                              Cont scopeRead N exportRead →
                                PkgSig bundle P pkg →
                                  PkgSig bundle N pkg →
                                    PkgSig bundle exportRead pkg →
                                      SemanticNameCert
                                          (fun row : BHist =>
                                            hsame row exportRead ∧ UnaryHistory row)
                                          (fun row : BHist =>
                                            hsame row X ∨ hsame row Y ∨ hsame row D ∨
                                              hsame row Z ∨ hsame row Q ∨ hsame row W ∨
                                                hsame row T ∨ hsame row E ∨ hsame row H ∨
                                                  hsame row C ∨ hsame row P ∨
                                                    hsame row N ∨ hsame row diffRead ∨
                                                      hsame row nullRead ∨
                                                        hsame row sealRead ∨
                                                          hsame row scopeRead ∨
                                                            hsame row exportRead)
                                          (fun row : BHist =>
                                            UnaryHistory row ∧ Cont D Z diffRead ∧
                                              Cont diffRead Q nullRead ∧
                                                Cont nullRead E sealRead ∧
                                                  Cont sealRead W scopeRead ∧
                                                    Cont scopeRead N exportRead ∧
                                                      PkgSig bundle exportRead pkg)
                                          hsame ∧
                                        UnaryHistory diffRead ∧ UnaryHistory nullRead ∧
                                          UnaryHistory sealRead ∧ UnaryHistory scopeRead ∧
                                            UnaryHistory exportRead := by
  -- BEDC touchpoint anchor: CauchyDifferenceCriterionUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro _xUnary _yUnary dUnary zUnary qUnary wUnary _tUnary eUnary nUnary
    diffRoute nullRoute sealRoute scopeRoute exportRoute _pPkg _nPkg exportPkg
  have diffUnary : UnaryHistory diffRead :=
    unary_cont_closed dUnary zUnary diffRoute
  have nullUnary : UnaryHistory nullRead :=
    unary_cont_closed diffUnary qUnary nullRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed nullUnary eUnary sealRoute
  have scopeUnary : UnaryHistory scopeRead :=
    unary_cont_closed sealUnary wUnary scopeRoute
  have exportUnary : UnaryHistory exportRead :=
    unary_cont_closed scopeUnary nUnary exportRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row exportRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row Y ∨ hsame row D ∨ hsame row Z ∨ hsame row Q ∨
              hsame row W ∨ hsame row T ∨ hsame row E ∨ hsame row H ∨ hsame row C ∨
                hsame row P ∨ hsame row N ∨ hsame row diffRead ∨ hsame row nullRead ∨
                  hsame row sealRead ∨ hsame row scopeRead ∨ hsame row exportRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D Z diffRead ∧ Cont diffRead Q nullRead ∧
              Cont nullRead E sealRead ∧ Cont sealRead W scopeRead ∧
                Cont scopeRead N exportRead ∧ PkgSig bundle exportRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro exportRead ⟨hsame_refl exportRead, exportUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr source.left)))))))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, diffRoute, nullRoute, sealRoute, scopeRoute, exportRoute,
          exportPkg⟩
  }
  exact ⟨cert, diffUnary, nullUnary, sealUnary, scopeUnary, exportUnary⟩

end BEDC.Derived.CauchyDifferenceCriterionUp
