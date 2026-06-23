import BEDC.Derived.LimsupUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LimsupUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LimsupTailCutRoute [AskSetup] [PackageSetup]
    {S U D T H C P N upperLedger tailLedger terminal named : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory S →
      UnaryHistory U →
        UnaryHistory D →
          UnaryHistory T →
            UnaryHistory H →
              Cont S U upperLedger →
                Cont upperLedger D tailLedger →
                  Cont tailLedger T terminal →
                    Cont terminal H named →
                      PkgSig bundle P pkg →
                        PkgSig bundle named pkg →
                          SemanticNameCert
                              (fun row : BHist => hsame row named ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row S ∨ hsame row U ∨ hsame row D ∨
                                  hsame row T ∨ hsame row upperLedger ∨
                                    hsame row tailLedger ∨ hsame row terminal ∨
                                      hsame row named)
                              (fun row : BHist =>
                                UnaryHistory row ∧ Cont S U upperLedger ∧
                                  Cont upperLedger D tailLedger ∧
                                    Cont tailLedger T terminal ∧ Cont terminal H named ∧
                                      PkgSig bundle named pkg)
                              hsame ∧
                            UnaryHistory upperLedger ∧ UnaryHistory tailLedger ∧
                              UnaryHistory terminal ∧ UnaryHistory named := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro sUnary uUnary dUnary tUnary hUnary upperRoute tailRoute terminalRoute namedRoute
    _provenancePkg namedPkg
  have upperUnary : UnaryHistory upperLedger :=
    unary_cont_closed sUnary uUnary upperRoute
  have tailUnary : UnaryHistory tailLedger :=
    unary_cont_closed upperUnary dUnary tailRoute
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed tailUnary tUnary terminalRoute
  have namedUnary : UnaryHistory named :=
    unary_cont_closed terminalUnary hUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row named ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row U ∨ hsame row D ∨ hsame row T ∨
              hsame row upperLedger ∨ hsame row tailLedger ∨ hsame row terminal ∨
                hsame row named)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S U upperLedger ∧ Cont upperLedger D tailLedger ∧
              Cont tailLedger T terminal ∧ Cont terminal H named ∧
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
                    (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, upperRoute, tailRoute, terminalRoute, namedRoute, namedPkg⟩
  }
  exact ⟨cert, upperUnary, tailUnary, terminalUnary, namedUnary⟩

end BEDC.Derived.LimsupUp
