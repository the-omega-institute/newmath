import BEDC.Derived.LimsupUp.TailCutRoute

namespace BEDC.Derived.LimsupUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LimsupTerminalSealRouting [AskSetup] [PackageSetup]
    {S U D T H C P N tailCut sealPrep terminalSeal named : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory S →
      UnaryHistory U →
        UnaryHistory D →
          UnaryHistory T →
            UnaryHistory H →
              Cont S U tailCut →
                Cont tailCut D sealPrep →
                  Cont sealPrep T terminalSeal →
                    Cont terminalSeal H named →
                      PkgSig bundle named pkg →
                        SemanticNameCert
                            (fun row : BHist => hsame row terminalSeal ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row S ∨ hsame row U ∨ hsame row D ∨ hsame row T ∨
                                hsame row tailCut ∨ hsame row sealPrep ∨
                                  hsame row terminalSeal ∨ hsame row named)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont S U tailCut ∧
                                Cont tailCut D sealPrep ∧ Cont sealPrep T terminalSeal ∧
                                  Cont terminalSeal H named ∧ PkgSig bundle named pkg)
                            hsame ∧
                          UnaryHistory tailCut ∧ UnaryHistory sealPrep ∧
                            UnaryHistory terminalSeal ∧ UnaryHistory named := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro sUnary uUnary dUnary tUnary hUnary tailRoute sealPrepRoute terminalSealRoute
    namedRoute namedPkg
  have tailUnary : UnaryHistory tailCut :=
    unary_cont_closed sUnary uUnary tailRoute
  have sealPrepUnary : UnaryHistory sealPrep :=
    unary_cont_closed tailUnary dUnary sealPrepRoute
  have terminalSealUnary : UnaryHistory terminalSeal :=
    unary_cont_closed sealPrepUnary tUnary terminalSealRoute
  have namedUnary : UnaryHistory named :=
    unary_cont_closed terminalSealUnary hUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row terminalSeal ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row U ∨ hsame row D ∨ hsame row T ∨
              hsame row tailCut ∨ hsame row sealPrep ∨ hsame row terminalSeal ∨
                hsame row named)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S U tailCut ∧ Cont tailCut D sealPrep ∧
              Cont sealPrep T terminalSeal ∧ Cont terminalSeal H named ∧
                PkgSig bundle named pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro terminalSeal
        ⟨hsame_refl terminalSeal, terminalSealUnary⟩
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
                    (Or.inl source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, tailRoute, sealPrepRoute, terminalSealRoute, namedRoute, namedPkg⟩
  }
  exact ⟨cert, tailUnary, sealPrepUnary, terminalSealUnary, namedUnary⟩

end BEDC.Derived.LimsupUp
