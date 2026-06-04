import BEDC.Derived.LowerSemicontinuousUp.RealHandoff

namespace BEDC.Derived.LowerSemicontinuousUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LowerSemicontinuousTransportReplayExactness [AskSetup] [PackageSetup]
    {X F E W R O H C P N transportRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] →
      UnaryHistory X → UnaryHistory F → UnaryHistory E → UnaryHistory W → UnaryHistory R →
        UnaryHistory O → UnaryHistory H → UnaryHistory C → Cont X H transportRead →
          Cont transportRead C replayRead → PkgSig bundle P pkg → PkgSig bundle N pkg →
            SemanticNameCert
                (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row X ∨ hsame row F ∨ hsame row E ∨ hsame row W ∨
                    hsame row R ∨ hsame row O ∨ hsame row H ∨ hsame row C ∨
                      hsame row P ∨ hsame row N ∨ hsame row transportRead ∨
                        hsame row replayRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont X H transportRead ∧
                    Cont transportRead C replayRead ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle N pkg)
                hsame ∧
              UnaryHistory transportRead ∧ UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro fields xUnary _fUnary _eUnary _wUnary _rUnary _oUnary hUnary cUnary
    transportRoute replayRoute provenancePkg namePkg
  have _acceptedFields :
      lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] := fields
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed xUnary hUnary transportRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed transportUnary cUnary replayRoute
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
        exact
          Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr source.left))))))))))
      ledger_sound := by
        intro _row source
        exact ⟨source.right, transportRoute, replayRoute, provenancePkg, namePkg⟩
    }
  · exact ⟨transportUnary, replayUnary⟩

end BEDC.Derived.LowerSemicontinuousUp
