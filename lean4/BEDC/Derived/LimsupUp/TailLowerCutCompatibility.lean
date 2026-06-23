import BEDC.Derived.LimsupUp.TailCutRoute

namespace BEDC.Derived.LimsupUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LimsupTailLowerCutCompatibility [AskSetup] [PackageSetup]
    {S U D T H C P N lowerLedger tailLedger terminal named : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory S →
      UnaryHistory U →
        UnaryHistory D →
          UnaryHistory T →
            UnaryHistory H →
              Cont U D lowerLedger →
                Cont S lowerLedger tailLedger →
                  Cont tailLedger T terminal →
                    Cont terminal H named →
                      PkgSig bundle named pkg →
                        SemanticNameCert
                            (fun row : BHist => hsame row named ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row U ∨ hsame row D ∨ hsame row lowerLedger ∨
                                hsame row tailLedger ∨ hsame row terminal ∨
                                  hsame row named)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont U D lowerLedger ∧
                                Cont S lowerLedger tailLedger ∧
                                  Cont tailLedger T terminal ∧ Cont terminal H named ∧
                                    PkgSig bundle named pkg)
                            hsame ∧
                          UnaryHistory lowerLedger ∧ UnaryHistory tailLedger ∧
                            UnaryHistory terminal ∧ UnaryHistory named := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro sUnary uUnary dUnary tUnary hUnary lowerRoute tailRoute terminalRoute namedRoute
    namedPkg
  have lowerUnary : UnaryHistory lowerLedger :=
    unary_cont_closed uUnary dUnary lowerRoute
  have tailUnary : UnaryHistory tailLedger :=
    unary_cont_closed sUnary lowerUnary tailRoute
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed tailUnary tUnary terminalRoute
  have namedUnary : UnaryHistory named :=
    unary_cont_closed terminalUnary hUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row named ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row U ∨ hsame row D ∨ hsame row lowerLedger ∨
              hsame row tailLedger ∨ hsame row terminal ∨ hsame row named)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont U D lowerLedger ∧
              Cont S lowerLedger tailLedger ∧ Cont tailLedger T terminal ∧
                Cont terminal H named ∧ PkgSig bundle named pkg)
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
      exact
        ⟨source.right, lowerRoute, tailRoute, terminalRoute, namedRoute, namedPkg⟩
  }
  exact ⟨cert, lowerUnary, tailUnary, terminalUnary, namedUnary⟩

end BEDC.Derived.LimsupUp
