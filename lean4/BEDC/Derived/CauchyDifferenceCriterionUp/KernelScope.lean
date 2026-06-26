import BEDC.Derived.CauchyDifferenceCriterionUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.CauchyDifferenceCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyDifferenceCriterionKernelScope [AskSetup] [PackageSetup]
    {X Y D Z Q W T E H C P N sourceRead diffRead nullRead sealRead scopeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory X ->
      UnaryHistory Y ->
        UnaryHistory D ->
          UnaryHistory Z ->
            UnaryHistory Q ->
              UnaryHistory W ->
                UnaryHistory T ->
                  UnaryHistory E ->
                    Cont X Y sourceRead ->
                      Cont D Z diffRead ->
                        Cont diffRead Q nullRead ->
                          Cont nullRead E sealRead ->
                            Cont sealRead W scopeRead ->
                              PkgSig bundle P pkg ->
                                PkgSig bundle scopeRead pkg ->
                                  cauchyDifferenceCriterionFromEventFlow
                                      (cauchyDifferenceCriterionToEventFlow
                                        (CauchyDifferenceCriterionUp.mk
                                          X Y D Z Q W T E H C P N)) =
                                    some
                                      (CauchyDifferenceCriterionUp.mk X Y D Z Q W T E H C P N) ->
                                    SemanticNameCert
                                        (fun row : BHist => hsame row scopeRead ∧ UnaryHistory row)
                                        (fun row : BHist =>
                                          hsame row X ∨ hsame row Y ∨ hsame row D ∨
                                            hsame row Z ∨ hsame row Q ∨ hsame row W ∨
                                              hsame row T ∨ hsame row E ∨
                                                hsame row scopeRead)
                                        (fun row : BHist =>
                                          UnaryHistory row ∧ PkgSig bundle P pkg ∧
                                            PkgSig bundle scopeRead pkg)
                                        hsame ∧
                                      UnaryHistory sourceRead ∧ UnaryHistory diffRead ∧
                                        UnaryHistory nullRead ∧ UnaryHistory sealRead ∧
                                          UnaryHistory scopeRead := by
  -- BEDC touchpoint anchor: CauchyDifferenceCriterionUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro xUnary yUnary dUnary zUnary qUnary wUnary tUnary eUnary sourceRoute diffRoute
    nullRoute sealRoute scopeRoute pPkg scopePkg _readback
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed xUnary yUnary sourceRoute
  have diffUnary : UnaryHistory diffRead :=
    unary_cont_closed dUnary zUnary diffRoute
  have nullUnary : UnaryHistory nullRead :=
    unary_cont_closed diffUnary qUnary nullRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed nullUnary eUnary sealRoute
  have scopeUnary : UnaryHistory scopeRead :=
    unary_cont_closed sealUnary wUnary scopeRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row scopeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row Y ∨ hsame row D ∨ hsame row Z ∨ hsame row Q ∨
              hsame row W ∨ hsame row T ∨ hsame row E ∨ hsame row scopeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle scopeRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro scopeRead ⟨hsame_refl scopeRead, scopeUnary⟩
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
                      (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, pPkg, scopePkg⟩
  }
  exact ⟨cert, sourceUnary, diffUnary, nullUnary, sealUnary, scopeUnary⟩

end BEDC.Derived.CauchyDifferenceCriterionUp
