import BEDC.Derived.RegularCauchyWindowFusionUp.TailWindowCoverage

namespace BEDC.Derived.RegularCauchyWindowFusionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyWindowFusionPublicExport [AskSetup] [PackageSetup]
    {R W S D E H C P N tailRead budgetRead sealRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory R ->
      UnaryHistory W ->
        UnaryHistory S ->
          UnaryHistory D ->
            UnaryHistory E ->
              UnaryHistory H ->
                Cont W S tailRead ->
                  Cont S D budgetRead ->
                    Cont tailRead budgetRead sealRead ->
                      Cont H sealRead publicRead ->
                        PkgSig bundle P pkg ->
                          PkgSig bundle publicRead pkg ->
                            SemanticNameCert
                                (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row R ∨ hsame row W ∨ hsame row S ∨
                                    hsame row D ∨ hsame row E ∨ hsame row H ∨
                                      hsame row C ∨ hsame row P ∨ hsame row N ∨
                                        hsame row tailRead ∨ hsame row budgetRead ∨
                                          hsame row sealRead ∨ hsame row publicRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont W S tailRead ∧
                                    Cont S D budgetRead ∧
                                      Cont tailRead budgetRead sealRead ∧
                                        Cont H sealRead publicRead ∧
                                          PkgSig bundle publicRead pkg)
                                hsame ∧
                              UnaryHistory tailRead ∧ UnaryHistory budgetRead ∧
                                UnaryHistory sealRead ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro _rUnary wUnary sUnary dUnary _eUnary hUnary tailRoute budgetRoute sealRoute
    publicRoute _packageRead publicPkg
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed wUnary sUnary tailRoute
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed sUnary dUnary budgetRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary budgetUnary sealRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed hUnary sealUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row R ∨ hsame row W ∨ hsame row S ∨ hsame row D ∨ hsame row E ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row tailRead ∨ hsame row budgetRead ∨ hsame row sealRead ∨
                  hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W S tailRead ∧ Cont S D budgetRead ∧
              Cont tailRead budgetRead sealRead ∧ Cont H sealRead publicRead ∧
                PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
      exact ⟨source.right, tailRoute, budgetRoute, sealRoute, publicRoute, publicPkg⟩
  }
  exact ⟨cert, tailUnary, budgetUnary, sealUnary, publicUnary⟩

end BEDC.Derived.RegularCauchyWindowFusionUp
