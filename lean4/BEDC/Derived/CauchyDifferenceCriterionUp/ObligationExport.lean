import BEDC.Derived.CauchyDifferenceCriterionUp.KernelScope

namespace BEDC.Derived.CauchyDifferenceCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyDifferenceCriterionObligationExport [AskSetup] [PackageSetup]
    {X Y D Z Q W T E H C P N diffRead nullRead zeroRead sealRead exportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    cauchyDifferenceCriterionFields (CauchyDifferenceCriterionUp.mk X Y D Z Q W T E H C P N) =
        [X, Y, D, Z, Q, W, T, E, H, C, P, N] →
      UnaryHistory D →
        UnaryHistory Z →
          UnaryHistory Q →
            UnaryHistory E →
              UnaryHistory N →
                Cont D Z diffRead →
                  Cont diffRead Q nullRead →
                    Cont nullRead E sealRead →
                      Cont sealRead N exportRead →
                        PkgSig bundle P pkg →
                          PkgSig bundle N pkg →
                            PkgSig bundle exportRead pkg →
                              SemanticNameCert
                                  (fun row : BHist =>
                                    hsame row exportRead ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row X ∨ hsame row Y ∨ hsame row D ∨
                                      hsame row Z ∨ hsame row Q ∨ hsame row W ∨
                                        hsame row T ∨ hsame row E ∨ hsame row N ∨
                                          hsame row diffRead ∨ hsame row nullRead ∨
                                            hsame row sealRead ∨ hsame row exportRead)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ Cont D Z diffRead ∧
                                      Cont diffRead Q nullRead ∧
                                        Cont nullRead E sealRead ∧
                                          Cont sealRead N exportRead ∧
                                            PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
                                              PkgSig bundle exportRead pkg)
                                  hsame ∧
                                UnaryHistory diffRead ∧ UnaryHistory nullRead ∧
                                  UnaryHistory sealRead ∧ UnaryHistory exportRead := by
  -- BEDC touchpoint anchor: CauchyDifferenceCriterionUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro fields_eq dUnary zUnary qUnary eUnary nUnary diffRoute nullRoute sealRoute exportRoute
    pPkg nPkg exportPkg
  have _zeroReadRow : BHist := zeroRead
  cases fields_eq
  have diffReadUnary : UnaryHistory diffRead :=
    unary_cont_closed dUnary zUnary diffRoute
  have nullReadUnary : UnaryHistory nullRead :=
    unary_cont_closed diffReadUnary qUnary nullRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed nullReadUnary eUnary sealRoute
  have exportReadUnary : UnaryHistory exportRead :=
    unary_cont_closed sealReadUnary nUnary exportRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row exportRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row Y ∨ hsame row D ∨ hsame row Z ∨ hsame row Q ∨
              hsame row W ∨ hsame row T ∨ hsame row E ∨ hsame row N ∨
                hsame row diffRead ∨ hsame row nullRead ∨ hsame row sealRead ∨
                  hsame row exportRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D Z diffRead ∧ Cont diffRead Q nullRead ∧
              Cont nullRead E sealRead ∧ Cont sealRead N exportRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧ PkgSig bundle exportRead pkg)
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
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, diffRoute, nullRoute, sealRoute, exportRoute, pPkg, nPkg,
          exportPkg⟩
  }
  exact ⟨cert, diffReadUnary, nullReadUnary, sealReadUnary, exportReadUnary⟩

end BEDC.Derived.CauchyDifferenceCriterionUp
