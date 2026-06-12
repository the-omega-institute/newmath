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

theorem LimitFiniteWindowExactness [AskSetup] [PackageSetup]
    {S R D A T C H P N windowRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    limitFields (LimitUp.mk S R D A T C H P N) =
        [S, R, D, A, T, C, H, P, N] ->
      UnaryHistory S ->
        UnaryHistory R ->
          UnaryHistory C ->
            UnaryHistory H ->
              Cont S R windowRead ->
                Cont windowRead C replayRead ->
                  hsame H replayRead ->
                    PkgSig bundle P pkg ->
                      PkgSig bundle N pkg ->
                        SemanticNameCert
                            (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row S ∨ hsame row R ∨ hsame row C ∨ hsame row H ∨
                                Cont S R windowRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont S R windowRead ∧
                                Cont windowRead C replayRead ∧ PkgSig bundle P pkg ∧
                                  PkgSig bundle N pkg)
                            hsame ∧
                          UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro fieldRows sUnary rUnary cUnary _hUnary windowRoute replayRoute sameHReplay
    provenancePkg namePkg
  cases fieldRows
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed sUnary rUnary windowRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed windowUnary cUnary replayRoute
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro replayRead (And.intro (hsame_refl replayRead) replayUnary)
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
          exact And.intro (hsame_trans (hsame_symm sameRows) source.left)
            (unary_transport source.right sameRows)
      }
      pattern_sound := by
        intro _row source
        exact Or.inr
          (Or.inr (Or.inr (Or.inl (hsame_trans source.left (hsame_symm sameHReplay)))))
      ledger_sound := by
        intro _row source
        exact ⟨source.right, windowRoute, replayRoute, provenancePkg, namePkg⟩
    }
  · exact replayUnary

end BEDC.Derived.LimitUp
