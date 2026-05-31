import BEDC.Derived.NormalFormConsistencySealUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.NormalFormConsistencySealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem NormalFormConsistencySealContinuationReplay [AskSetup] [PackageSetup]
    {T F N K X H C P L typedRead falseRead normalRead theoremRead boundaryRead
      transportRead replayRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory T →
      UnaryHistory F →
        UnaryHistory N →
          UnaryHistory K →
            UnaryHistory X →
              UnaryHistory H →
                UnaryHistory C →
                  UnaryHistory P →
                    UnaryHistory L →
                      Cont T F typedRead →
                        Cont typedRead N normalRead →
                          Cont normalRead K theoremRead →
                            Cont theoremRead X boundaryRead →
                              Cont boundaryRead H transportRead →
                                Cont transportRead C replayRead →
                                  Cont replayRead L namedRead →
                                    PkgSig bundle P pkg →
                                      PkgSig bundle L pkg →
                                        SemanticNameCert
                                            (fun row : BHist =>
                                              hsame row replayRead ∧ UnaryHistory row)
                                            (fun row : BHist =>
                                              hsame row T ∨ hsame row F ∨ hsame row N ∨
                                                hsame row K ∨ hsame row X ∨
                                                  hsame row replayRead)
                                            (fun row : BHist =>
                                              UnaryHistory row ∧
                                                Cont boundaryRead H transportRead ∧
                                                  Cont transportRead C replayRead ∧
                                                    PkgSig bundle P pkg ∧
                                                      PkgSig bundle L pkg)
                                            hsame ∧
                                          UnaryHistory replayRead ∧
                                            UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg SemanticNameCert UnaryHistory
  intro tUnary fUnary nUnary kUnary xUnary hUnary cUnary _pUnary lUnary typedRoute
    normalRoute theoremRoute boundaryRoute transportRoute replayRoute namedRoute
    provenancePkg namePkg
  have typedUnary : UnaryHistory typedRead :=
    unary_cont_closed tUnary fUnary typedRoute
  have normalUnary : UnaryHistory normalRead :=
    unary_cont_closed typedUnary nUnary normalRoute
  have theoremUnary : UnaryHistory theoremRead :=
    unary_cont_closed normalUnary kUnary theoremRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed theoremUnary xUnary boundaryRoute
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed boundaryUnary hUnary transportRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed transportUnary cUnary replayRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed replayUnary lUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row F ∨ hsame row N ∨ hsame row K ∨ hsame row X ∨
              hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont boundaryRead H transportRead ∧
              Cont transportRead C replayRead ∧ PkgSig bundle P pkg ∧
                PkgSig bundle L pkg)
          hsame := {
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, transportRoute, replayRoute, provenancePkg, namePkg⟩
  }
  exact ⟨cert, replayUnary, namedUnary⟩

end BEDC.Derived.NormalFormConsistencySealUp
