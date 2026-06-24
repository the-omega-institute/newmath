import BEDC.Derived.RegularCauchyWindowFusionUp.NameCertObligations

namespace BEDC.Derived.RegularCauchyWindowFusionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyWindowFusionKernelScope [AskSetup] [PackageSetup]
    {R W S D E H C P N tailRead budgetRead sealRead kernelRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory R ->
      UnaryHistory W ->
        UnaryHistory S ->
          UnaryHistory D ->
            UnaryHistory E ->
              UnaryHistory H ->
                UnaryHistory C ->
                  UnaryHistory P ->
                    UnaryHistory N ->
                      Cont W S tailRead ->
                        Cont S D budgetRead ->
                          Cont tailRead budgetRead sealRead ->
                            Cont sealRead C kernelRead ->
                              PkgSig bundle P pkg ->
                                PkgSig bundle N pkg ->
                                  SemanticNameCert
                                      (fun row : BHist =>
                                        hsame row kernelRead ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row R ∨ hsame row W ∨ hsame row S ∨
                                          hsame row D ∨ hsame row E ∨ hsame row H ∨
                                            hsame row C ∨ hsame row P ∨ hsame row N ∨
                                              hsame row tailRead ∨
                                                hsame row budgetRead ∨
                                                  hsame row sealRead ∨
                                                    hsame row kernelRead)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧ Cont W S tailRead ∧
                                          Cont S D budgetRead ∧
                                            Cont tailRead budgetRead sealRead ∧
                                              Cont sealRead C kernelRead ∧
                                                PkgSig bundle P pkg ∧
                                                  PkgSig bundle N pkg)
                                      hsame ∧
                                    UnaryHistory tailRead ∧ UnaryHistory budgetRead ∧
                                      UnaryHistory sealRead ∧
                                        UnaryHistory kernelRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro _rUnary wUnary sUnary dUnary _eUnary _hUnary cUnary _pUnary _nUnary
    tailRoute budgetRoute sealRoute kernelRoute pkgP pkgN
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed wUnary sUnary tailRoute
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed sUnary dUnary budgetRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary budgetUnary sealRoute
  have kernelUnary : UnaryHistory kernelRead :=
    unary_cont_closed sealUnary cUnary kernelRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row kernelRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row R ∨ hsame row W ∨ hsame row S ∨ hsame row D ∨ hsame row E ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row tailRead ∨ hsame row budgetRead ∨ hsame row sealRead ∨
                  hsame row kernelRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W S tailRead ∧ Cont S D budgetRead ∧
              Cont tailRead budgetRead sealRead ∧ Cont sealRead C kernelRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro kernelRead ⟨hsame_refl kernelRead, kernelUnary⟩
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
        ⟨source.right, tailRoute, budgetRoute, sealRoute, kernelRoute, pkgP, pkgN⟩
  }
  exact ⟨cert, tailUnary, budgetUnary, sealUnary, kernelUnary⟩

end BEDC.Derived.RegularCauchyWindowFusionUp
