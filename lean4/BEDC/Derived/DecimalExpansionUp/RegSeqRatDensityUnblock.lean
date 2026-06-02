import BEDC.Derived.DecimalExpansionUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DecimalExpansionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DecimalExpansionRegSeqRatDensityUnblock [AskSetup] [PackageSetup]
    {D W V Q R E H C P N prefixRead placeRead toleranceRead regRead sealRead
      densityRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory D ->
      UnaryHistory W ->
        UnaryHistory V ->
          UnaryHistory Q ->
            UnaryHistory R ->
              UnaryHistory E ->
                UnaryHistory H ->
                  Cont D W prefixRead ->
                    Cont prefixRead V placeRead ->
                      Cont placeRead Q toleranceRead ->
                        Cont toleranceRead R regRead ->
                          Cont regRead E sealRead ->
                            Cont sealRead H densityRead ->
                              PkgSig bundle P pkg ->
                                PkgSig bundle N pkg ->
                                  SemanticNameCert
                                      (fun row : BHist =>
                                        hsame row densityRead ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row D ∨ hsame row W ∨ hsame row V ∨
                                          hsame row Q ∨ hsame row R ∨ hsame row E ∨
                                            hsame row densityRead)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧ PkgSig bundle P pkg ∧
                                          PkgSig bundle N pkg)
                                      hsame ∧
                                    UnaryHistory prefixRead ∧ UnaryHistory placeRead ∧
                                      UnaryHistory toleranceRead ∧ UnaryHistory regRead ∧
                                        UnaryHistory sealRead ∧
                                          UnaryHistory densityRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame UnaryHistory
  intro dUnary wUnary vUnary qUnary rUnary eUnary hUnary
  intro prefixRoute placeRoute toleranceRoute regRoute sealRoute densityRoute
  intro provenancePkg namePkg
  have prefixReadUnary : UnaryHistory prefixRead :=
    unary_cont_closed dUnary wUnary prefixRoute
  have placeReadUnary : UnaryHistory placeRead :=
    unary_cont_closed prefixReadUnary vUnary placeRoute
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed placeReadUnary qUnary toleranceRoute
  have regReadUnary : UnaryHistory regRead :=
    unary_cont_closed toleranceReadUnary rUnary regRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed regReadUnary eUnary sealRoute
  have densityReadUnary : UnaryHistory densityRead :=
    unary_cont_closed sealReadUnary hUnary densityRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row densityRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row W ∨ hsame row V ∨ hsame row Q ∨
              hsame row R ∨ hsame row E ∨ hsame row densityRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro densityRead
        ⟨hsame_refl densityRead, densityReadUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _left _middle _right sameLeft sameRight
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
    ⟨cert, prefixReadUnary, placeReadUnary, toleranceReadUnary, regReadUnary,
      sealReadUnary, densityReadUnary⟩

end BEDC.Derived.DecimalExpansionUp
