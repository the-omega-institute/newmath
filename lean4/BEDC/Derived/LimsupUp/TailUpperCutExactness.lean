import BEDC.Derived.LimsupUp.TailCutRoute

namespace BEDC.Derived.LimsupUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LimsupTailUpperCutExactness [AskSetup] [PackageSetup]
    {S U T H upperLedger upperRead named : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory S →
      UnaryHistory U →
        UnaryHistory T →
          UnaryHistory H →
            Cont S U upperLedger →
              Cont upperLedger H upperRead →
                Cont upperRead T named →
                  PkgSig bundle named pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row named ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row S ∨ hsame row U ∨ hsame row upperLedger ∨
                            hsame row upperRead ∨ hsame row T ∨ hsame row named)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont S U upperLedger ∧
                            Cont upperLedger H upperRead ∧ Cont upperRead T named ∧
                              PkgSig bundle named pkg)
                        hsame ∧
                      UnaryHistory upperLedger ∧ UnaryHistory upperRead ∧
                        UnaryHistory named := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro sUnary uUnary tUnary hUnary upperRoute readRoute namedRoute namedPkg
  have upperUnary : UnaryHistory upperLedger :=
    unary_cont_closed sUnary uUnary upperRoute
  have readUnary : UnaryHistory upperRead :=
    unary_cont_closed upperUnary hUnary readRoute
  have namedUnary : UnaryHistory named :=
    unary_cont_closed readUnary tUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row named ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row U ∨ hsame row upperLedger ∨
              hsame row upperRead ∨ hsame row T ∨ hsame row named)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S U upperLedger ∧
              Cont upperLedger H upperRead ∧ Cont upperRead T named ∧
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, upperRoute, readRoute, namedRoute, namedPkg⟩
  }
  exact ⟨cert, upperUnary, readUnary, namedUnary⟩

end BEDC.Derived.LimsupUp
