import BEDC.Derived.DecimalExpansionUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.DecimalExpansionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DecimalExpansionTerminalCarryRefusal [AskSetup] [PackageSetup]
    {D W V Q R E H C P N carryRead placeRead toleranceRead regRead sealedRead
      refusedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory D →
      UnaryHistory W →
        UnaryHistory V →
          UnaryHistory Q →
            UnaryHistory R →
              UnaryHistory E →
                UnaryHistory H →
                  Cont D W carryRead →
                    Cont carryRead V placeRead →
                      Cont placeRead Q toleranceRead →
                        Cont toleranceRead R regRead →
                          Cont regRead E sealedRead →
                            Cont sealedRead H refusedRead →
                              PkgSig bundle P pkg →
                                PkgSig bundle N pkg →
                                  SemanticNameCert
                                      (fun row : BHist =>
                                        hsame row refusedRead ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row D ∨ hsame row W ∨ hsame row V ∨
                                          hsame row Q ∨ hsame row R ∨ hsame row E ∨
                                            hsame row refusedRead)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧ PkgSig bundle P pkg ∧
                                          PkgSig bundle N pkg)
                                      hsame ∧
                                    UnaryHistory carryRead ∧ UnaryHistory placeRead ∧
                                      UnaryHistory toleranceRead ∧ UnaryHistory regRead ∧
                                        UnaryHistory sealedRead ∧
                                          UnaryHistory refusedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro dUnary wUnary vUnary qUnary rUnary eUnary hUnary carryRoute placeRoute
    toleranceRoute regRoute sealRoute refusalRoute provenancePkg namePkg
  have carryUnary : UnaryHistory carryRead :=
    unary_cont_closed dUnary wUnary carryRoute
  have placeUnary : UnaryHistory placeRead :=
    unary_cont_closed carryUnary vUnary placeRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed placeUnary qUnary toleranceRoute
  have regUnary : UnaryHistory regRead :=
    unary_cont_closed toleranceUnary rUnary regRoute
  have sealedUnary : UnaryHistory sealedRead :=
    unary_cont_closed regUnary eUnary sealRoute
  have refusedUnary : UnaryHistory refusedRead :=
    unary_cont_closed sealedUnary hUnary refusalRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row refusedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row W ∨ hsame row V ∨ hsame row Q ∨ hsame row R ∨
              hsame row E ∨ hsame row refusedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro refusedRead ⟨hsame_refl refusedRead, refusedUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, namePkg⟩
  }
  exact
    ⟨cert, carryUnary, placeUnary, toleranceUnary, regUnary, sealedUnary,
      refusedUnary⟩

end BEDC.Derived.DecimalExpansionUp
