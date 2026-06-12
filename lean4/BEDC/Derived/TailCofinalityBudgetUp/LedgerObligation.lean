import BEDC.Derived.TailCofinalityBudgetUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.TailCofinalityBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TailCofinalityBudgetLedgerObligation [AskSetup] [PackageSetup]
    {x : TailCofinalityBudgetUp} {R W D Q E H C P N ledgerRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    tailCofinalityBudgetFields x = [R, W, D, Q, E, H, C, P, N] →
      UnaryHistory R →
        UnaryHistory W →
          UnaryHistory D →
            UnaryHistory Q →
              UnaryHistory E →
                Cont R W ledgerRead →
                  Cont ledgerRead D sealRead →
                    PkgSig bundle P pkg →
                      PkgSig bundle N pkg →
                        SemanticNameCert
                            (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row R ∨ hsame row W ∨ hsame row D ∨
                                hsame row Q ∨ hsame row E ∨ hsame row sealRead)
                            (fun row : BHist =>
                              PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
                                hsame row sealRead)
                            hsame ∧
                          UnaryHistory ledgerRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame SemanticNameCert
  intro _fieldRows rUnary wUnary dUnary _qUnary _eUnary ledgerRoute sealRoute pPkg nPkg
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed rUnary wUnary ledgerRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed ledgerUnary dUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row R ∨ hsame row W ∨ hsame row D ∨
              hsame row Q ∨ hsame row E ∨ hsame row sealRead)
          (fun row : BHist =>
            PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧ hsame row sealRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨pPkg, nPkg, source.left⟩
  }
  exact ⟨cert, ledgerUnary, sealUnary⟩

end BEDC.Derived.TailCofinalityBudgetUp
