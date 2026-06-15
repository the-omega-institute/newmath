import BEDC.Derived.LimitUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LimitUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LimitRegseqratRealScope [AskSetup] [PackageSetup]
    {S R D A T C H P N windowRead toleranceRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    limitFields (LimitUp.mk S R D A T C H P N) = [S, R, D, A, T, C, H, P, N] ->
      UnaryHistory S ->
        UnaryHistory R ->
          UnaryHistory D ->
            UnaryHistory A ->
              Cont S R windowRead ->
                Cont windowRead D toleranceRead ->
                  Cont toleranceRead A realRead ->
                    PkgSig bundle P pkg ->
                      PkgSig bundle N pkg ->
                        SemanticNameCert
                            (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row S ∨ hsame row R ∨ hsame row D ∨ hsame row A ∨
                                hsame row realRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont S R windowRead ∧
                                Cont windowRead D toleranceRead ∧
                                  Cont toleranceRead A realRead ∧ PkgSig bundle P pkg ∧
                                    PkgSig bundle N pkg)
                            hsame ∧
                          UnaryHistory realRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro fieldRows sUnary rUnary dUnary aUnary windowRoute toleranceRoute realRoute
    provenancePkg namePkg
  cases fieldRows
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed sUnary rUnary windowRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed windowUnary dUnary toleranceRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed toleranceUnary aUnary realRoute
  constructor
  · exact {
      core := {
        carrier_inhabited := Exists.intro realRead ⟨hsame_refl realRead, realUnary⟩
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
        exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, windowRoute, toleranceRoute, realRoute, provenancePkg, namePkg⟩
    }
  · exact realUnary

end BEDC.Derived.LimitUp
