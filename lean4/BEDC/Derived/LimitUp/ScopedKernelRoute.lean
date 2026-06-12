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

theorem LimitScopedKernelRoute [AskSetup] [PackageSetup]
    {S R D A T C H P N windowRead toleranceRead sealRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    limitFields (LimitUp.mk S R D A T C H P N) = [S, R, D, A, T, C, H, P, N] →
      UnaryHistory S →
        UnaryHistory R →
          UnaryHistory D →
            UnaryHistory A →
              UnaryHistory C →
                Cont S R windowRead →
                  Cont windowRead D toleranceRead →
                    Cont toleranceRead A sealRead →
                      Cont sealRead C replayRead →
                        PkgSig bundle P pkg →
                          PkgSig bundle N pkg →
                            SemanticNameCert
                                (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row S ∨ hsame row R ∨ hsame row D ∨
                                    hsame row A ∨ hsame row T ∨ hsame row C ∨
                                      hsame row H ∨ hsame row P ∨ hsame row N ∨
                                        hsame row replayRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont S R windowRead ∧
                                    Cont windowRead D toleranceRead ∧
                                      Cont toleranceRead A sealRead ∧
                                        Cont sealRead C replayRead ∧
                                          PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                                hsame ∧
                              UnaryHistory windowRead ∧ UnaryHistory toleranceRead ∧
                                UnaryHistory sealRead ∧ UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: LimitUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro fieldRows sUnary rUnary dUnary aUnary cUnary windowRoute toleranceRoute sealRoute
    replayRoute provenancePkg namePkg
  cases fieldRows
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed sUnary rUnary windowRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed windowUnary dUnary toleranceRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed toleranceUnary aUnary sealRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed sealUnary cUnary replayRoute
  constructor
  · exact {
      core := {
        carrier_inhabited := Exists.intro replayRead ⟨hsame_refl replayRead, replayUnary⟩
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
        exact Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr source.left))))))))
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, windowRoute, toleranceRoute, sealRoute, replayRoute, provenancePkg,
            namePkg⟩
    }
  · exact ⟨windowUnary, toleranceUnary, sealUnary, replayUnary⟩

end BEDC.Derived.LimitUp
