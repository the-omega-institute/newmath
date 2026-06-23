import BEDC.Derived.RegularCauchyWindowFusionUp.TailWindowCoverage

namespace BEDC.Derived.RegularCauchyWindowFusionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyWindowFusionTailHandoff [AskSetup] [PackageSetup]
    {W S D E H tailRead budgetRead sealRead named : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory W →
      UnaryHistory S →
        UnaryHistory D →
          UnaryHistory E →
            UnaryHistory H →
              Cont W S tailRead →
                Cont tailRead D budgetRead →
                  Cont budgetRead E sealRead →
                    Cont H sealRead named →
                      PkgSig bundle named pkg →
                        SemanticNameCert
                            (fun row : BHist => hsame row named ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row W ∨ hsame row S ∨ hsame row D ∨
                                hsame row E ∨ hsame row H ∨ hsame row tailRead ∨
                                  hsame row budgetRead ∨ hsame row sealRead ∨
                                    hsame row named)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont W S tailRead ∧
                                Cont tailRead D budgetRead ∧
                                  Cont budgetRead E sealRead ∧
                                    Cont H sealRead named ∧ PkgSig bundle named pkg)
                            hsame ∧
                          UnaryHistory tailRead ∧ UnaryHistory budgetRead ∧
                            UnaryHistory sealRead ∧ UnaryHistory named := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro wUnary sUnary dUnary eUnary hUnary tailRoute budgetRoute sealRoute namedRoute
    namedPkg
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed wUnary sUnary tailRoute
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed tailUnary dUnary budgetRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed budgetUnary eUnary sealRoute
  have namedUnary : UnaryHistory named :=
    unary_cont_closed hUnary sealUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row named ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row W ∨ hsame row S ∨ hsame row D ∨ hsame row E ∨ hsame row H ∨
              hsame row tailRead ∨ hsame row budgetRead ∨ hsame row sealRead ∨
                hsame row named)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W S tailRead ∧ Cont tailRead D budgetRead ∧
              Cont budgetRead E sealRead ∧ Cont H sealRead named ∧
                PkgSig bundle named pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro named ⟨hsame_refl named, namedUnary⟩
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
      exact ⟨source.right, tailRoute, budgetRoute, sealRoute, namedRoute, namedPkg⟩
  }
  exact ⟨cert, tailUnary, budgetUnary, sealUnary, namedUnary⟩

end BEDC.Derived.RegularCauchyWindowFusionUp
