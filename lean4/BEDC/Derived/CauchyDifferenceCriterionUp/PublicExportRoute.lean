import BEDC.Derived.CauchyDifferenceCriterionUp.PublicExactness

namespace BEDC.Derived.CauchyDifferenceCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyDifferenceCriterionPublicExport [AskSetup] [PackageSetup]
    {X Y D Z Q W T E H C P N diffRead nullRead sealRead exportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory D ->
      UnaryHistory Z ->
        UnaryHistory Q ->
          UnaryHistory E ->
            UnaryHistory C ->
              Cont D Z diffRead ->
                Cont diffRead Q nullRead ->
                  Cont nullRead E sealRead ->
                    Cont sealRead C exportRead ->
                      PkgSig bundle P pkg ->
                        PkgSig bundle N pkg ->
                          SemanticNameCert
                              (fun row : BHist => hsame row exportRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row X ∨ hsame row Y ∨ hsame row D ∨
                                  hsame row Z ∨ hsame row Q ∨ hsame row W ∨
                                    hsame row T ∨ hsame row E ∨ hsame row H ∨
                                      hsame row C ∨ hsame row P ∨ hsame row N ∨
                                        hsame row exportRead)
                              (fun row : BHist =>
                                UnaryHistory row ∧ Cont D Z diffRead ∧
                                  Cont diffRead Q nullRead ∧
                                    Cont nullRead E sealRead ∧
                                      Cont sealRead C exportRead ∧
                                        PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                              hsame ∧
                            UnaryHistory exportRead := by
  -- BEDC touchpoint anchor: CauchyDifferenceCriterionUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro dUnary zUnary qUnary eUnary cUnary diffRoute nullRoute sealRoute exportRoute
    pPkg nPkg
  have diffReadUnary : UnaryHistory diffRead :=
    unary_cont_closed dUnary zUnary diffRoute
  have nullReadUnary : UnaryHistory nullRead :=
    unary_cont_closed diffReadUnary qUnary nullRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed nullReadUnary eUnary sealRoute
  have exportReadUnary : UnaryHistory exportRead :=
    unary_cont_closed sealReadUnary cUnary exportRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row exportRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row Y ∨ hsame row D ∨ hsame row Z ∨ hsame row Q ∨
              hsame row W ∨ hsame row T ∨ hsame row E ∨ hsame row H ∨ hsame row C ∨
                hsame row P ∨ hsame row N ∨ hsame row exportRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D Z diffRead ∧ Cont diffRead Q nullRead ∧
              Cont nullRead E sealRead ∧ Cont sealRead C exportRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro exportRead ⟨hsame_refl exportRead, exportReadUnary⟩
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
                              (Or.inr source.left)))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, diffRoute, nullRoute, sealRoute, exportRoute, pPkg, nPkg⟩
  }
  exact ⟨cert, exportReadUnary⟩

end BEDC.Derived.CauchyDifferenceCriterionUp
