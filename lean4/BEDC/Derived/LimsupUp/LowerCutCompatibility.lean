import BEDC.Derived.LimsupUp.TailCutRoute

namespace BEDC.Derived.LimsupUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem Limsup_tail_lower_cut_compatibility [AskSetup] [PackageSetup]
    {S U D H P lowerLedger lowerRead upperLedger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory S →
      UnaryHistory U →
        UnaryHistory D →
          UnaryHistory H →
            Cont S U upperLedger →
              Cont S D lowerLedger →
                Cont lowerLedger H lowerRead →
                  PkgSig bundle P pkg →
                    PkgSig bundle lowerRead pkg →
                      SemanticNameCert
                          (fun row : BHist => hsame row lowerRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row S ∨ hsame row U ∨ hsame row D ∨
                              hsame row upperLedger ∨ hsame row lowerLedger ∨
                                hsame row lowerRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont S U upperLedger ∧
                              Cont S D lowerLedger ∧ Cont lowerLedger H lowerRead ∧
                                PkgSig bundle lowerRead pkg)
                          hsame ∧
                        UnaryHistory upperLedger ∧ UnaryHistory lowerLedger ∧
                          UnaryHistory lowerRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro sUnary uUnary dUnary hUnary upperRoute lowerRoute lowerReadRoute _sourcePkg
    lowerReadPkg
  have upperUnary : UnaryHistory upperLedger :=
    unary_cont_closed sUnary uUnary upperRoute
  have lowerLedgerUnary : UnaryHistory lowerLedger :=
    unary_cont_closed sUnary dUnary lowerRoute
  have lowerReadUnary : UnaryHistory lowerRead :=
    unary_cont_closed lowerLedgerUnary hUnary lowerReadRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row lowerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row U ∨ hsame row D ∨ hsame row upperLedger ∨
              hsame row lowerLedger ∨ hsame row lowerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S U upperLedger ∧ Cont S D lowerLedger ∧
              Cont lowerLedger H lowerRead ∧ PkgSig bundle lowerRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro lowerRead ⟨hsame_refl lowerRead, lowerReadUnary⟩
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
      exact ⟨source.right, upperRoute, lowerRoute, lowerReadRoute, lowerReadPkg⟩
  }
  exact ⟨cert, upperUnary, lowerLedgerUnary, lowerReadUnary⟩

end BEDC.Derived.LimsupUp
