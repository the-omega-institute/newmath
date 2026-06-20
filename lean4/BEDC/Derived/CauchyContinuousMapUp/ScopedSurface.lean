import BEDC.Derived.CauchyContinuousMapUp

namespace BEDC.Derived.CauchyContinuousMapUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyContinuousMap_scoped_surface [AskSetup] [PackageSetup]
    {W R D E H C P N windowRead toleranceRead sealRead replayRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory W ->
      UnaryHistory R ->
        UnaryHistory D ->
          UnaryHistory E ->
            UnaryHistory H ->
              UnaryHistory C ->
                UnaryHistory N ->
                  PkgSig bundle P pkg ->
                    PkgSig bundle N pkg ->
                      Cont W R windowRead ->
                        Cont windowRead D toleranceRead ->
                          Cont toleranceRead E sealRead ->
                            Cont H C replayRead ->
                              Cont sealRead N namedRead ->
                                SemanticNameCert
                                    (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row W ∨ hsame row R ∨ hsame row D ∨
                                        hsame row E ∨ hsame row H ∨ hsame row C ∨
                                          hsame row N ∨ hsame row namedRead)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ Cont W R windowRead ∧
                                        Cont windowRead D toleranceRead ∧
                                          Cont toleranceRead E sealRead ∧
                                            Cont H C replayRead ∧
                                              Cont sealRead N namedRead ∧
                                                PkgSig bundle P pkg ∧
                                                  PkgSig bundle N pkg)
                                    hsame ∧
                                  UnaryHistory windowRead ∧ UnaryHistory toleranceRead ∧
                                    UnaryHistory sealRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro wUnary rUnary dUnary eUnary hUnary cUnary nUnary sourcePkg namePkg windowRoute
    toleranceRoute sealRoute replayRoute namedRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed wUnary rUnary windowRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed windowUnary dUnary toleranceRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed toleranceUnary eUnary sealRoute
  have _replayUnary : UnaryHistory replayRead :=
    unary_cont_closed hUnary cUnary replayRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed sealUnary nUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row W ∨ hsame row R ∨ hsame row D ∨ hsame row E ∨ hsame row H ∨
              hsame row C ∨ hsame row N ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W R windowRead ∧ Cont windowRead D toleranceRead ∧
              Cont toleranceRead E sealRead ∧ Cont H C replayRead ∧
                Cont sealRead N namedRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, windowRoute, toleranceRoute, sealRoute, replayRoute, namedRoute,
          sourcePkg, namePkg⟩
  }
  exact ⟨cert, windowUnary, toleranceUnary, sealUnary, namedUnary⟩

end BEDC.Derived.CauchyContinuousMapUp
