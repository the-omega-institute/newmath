import BEDC.Derived.LimsupUp.TailCutRoute

namespace BEDC.Derived.LimsupUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LimsupRealSealNonescape [AskSetup] [PackageSetup]
    {S U D T H C P N tailCut sealRead named : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory S →
      UnaryHistory U →
        UnaryHistory D →
          UnaryHistory T →
            UnaryHistory H →
              Cont S U tailCut →
                Cont tailCut D sealRead →
                  Cont H sealRead named →
                    PkgSig bundle named pkg →
                      SemanticNameCert
                          (fun row : BHist => hsame row named ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row S ∨ hsame row U ∨ hsame row D ∨
                              hsame row T ∨ hsame row H ∨ hsame row C ∨
                                hsame row P ∨ hsame row N ∨ hsame row tailCut ∨
                                  hsame row sealRead ∨ hsame row named)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont S U tailCut ∧
                              Cont tailCut D sealRead ∧ Cont H sealRead named ∧
                                PkgSig bundle named pkg)
                          hsame ∧
                        UnaryHistory tailCut ∧ UnaryHistory sealRead ∧
                          UnaryHistory named := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro sUnary uUnary dUnary _tUnary hUnary tailRoute sealRoute namedRoute namedPkg
  have tailCutUnary : UnaryHistory tailCut :=
    unary_cont_closed sUnary uUnary tailRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed tailCutUnary dUnary sealRoute
  have namedUnary : UnaryHistory named :=
    unary_cont_closed hUnary sealReadUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row named ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row U ∨ hsame row D ∨ hsame row T ∨ hsame row H ∨
              hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row tailCut ∨
                hsame row sealRead ∨ hsame row named)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S U tailCut ∧ Cont tailCut D sealRead ∧
              Cont H sealRead named ∧ PkgSig bundle named pkg)
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
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
                          (Or.inr sourceRow.left)))))))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, tailRoute, sealRoute, namedRoute, namedPkg⟩
  }
  exact ⟨cert, tailCutUnary, sealReadUnary, namedUnary⟩

end BEDC.Derived.LimsupUp
