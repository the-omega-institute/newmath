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

theorem DecimalExpansionRegSeqRatPrefixCoverage [AskSetup] [PackageSetup]
    {D W V Q R E H C P N prefixRead placeRead toleranceRead regRead sealedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory D ->
      UnaryHistory W ->
        UnaryHistory V ->
          UnaryHistory Q ->
            UnaryHistory R ->
              UnaryHistory E ->
                UnaryHistory H ->
                  UnaryHistory C ->
                Cont D W prefixRead ->
                  Cont prefixRead V placeRead ->
                    Cont placeRead Q toleranceRead ->
                      Cont toleranceRead R regRead ->
                        Cont regRead E sealedRead ->
                          PkgSig bundle P pkg ->
                            PkgSig bundle N pkg ->
                              SemanticNameCert
                                  (fun row : BHist => hsame row regRead ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row D ∨ hsame row W ∨ hsame row V ∨
                                      hsame row Q ∨ hsame row R ∨ hsame row regRead)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ PkgSig bundle P pkg ∧
                                      PkgSig bundle N pkg)
                                  hsame ∧
                                UnaryHistory prefixRead ∧ UnaryHistory placeRead ∧
                                  UnaryHistory toleranceRead ∧ UnaryHistory regRead ∧
                                    UnaryHistory sealedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory hsame SemanticNameCert
  intro dUnary wUnary vUnary qUnary rUnary eUnary _hUnary _cUnary
  intro prefixRoute placeRoute toleranceRoute regRoute sealRoute provenancePkg namePkg
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed dUnary wUnary prefixRoute
  have placeUnary : UnaryHistory placeRead :=
    unary_cont_closed prefixUnary vUnary placeRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed placeUnary qUnary toleranceRoute
  have regUnary : UnaryHistory regRead :=
    unary_cont_closed toleranceUnary rUnary regRoute
  have sealUnary : UnaryHistory sealedRead :=
    unary_cont_closed regUnary eUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row regRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row W ∨ hsame row V ∨ hsame row Q ∨ hsame row R ∨
              hsame row regRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro regRead ⟨hsame_refl regRead, regUnary⟩
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
      exact ⟨source.right, provenancePkg, namePkg⟩
  }
  exact ⟨cert, prefixUnary, placeUnary, toleranceUnary, regUnary, sealUnary⟩

end BEDC.Derived.DecimalExpansionUp
