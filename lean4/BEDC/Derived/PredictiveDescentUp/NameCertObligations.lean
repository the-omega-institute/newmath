import BEDC.Derived.PredictiveDescentUp.StabilityScope
import BEDC.FKernel.NameCert

namespace BEDC.Derived.PredictiveDescentUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PredictiveDescentNameCertObligations [AskSetup] [PackageSetup]
    {F O K A S X H C P N opRead scopeRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory F →
      UnaryHistory O →
        UnaryHistory K →
          UnaryHistory A →
            UnaryHistory S →
              UnaryHistory X →
                Cont O A opRead →
                  Cont A K scopeRead →
                    Cont scopeRead S replayRead →
                      PkgSig bundle P pkg →
                        SemanticNameCert
                            (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row F ∨ hsame row O ∨ hsame row K ∨ hsame row A ∨
                                hsame row S ∨ hsame row X ∨ hsame row opRead ∨
                                  hsame row scopeRead ∨ hsame row replayRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont O A opRead ∧ Cont A K scopeRead ∧
                                Cont scopeRead S replayRead ∧ PkgSig bundle P pkg)
                            hsame ∧
                          UnaryHistory opRead ∧
                            UnaryHistory scopeRead ∧ UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert UnaryHistory
  intro _fUnary oUnary kUnary aUnary sUnary _xUnary opRoute scopeRoute replayRoute
    provenancePkg
  have opUnary : UnaryHistory opRead :=
    unary_cont_closed oUnary aUnary opRoute
  have scopeUnary : UnaryHistory scopeRead :=
    unary_cont_closed aUnary kUnary scopeRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed scopeUnary sUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row F ∨ hsame row O ∨ hsame row K ∨ hsame row A ∨ hsame row S ∨
              hsame row X ∨ hsame row opRead ∨ hsame row scopeRead ∨
                hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont O A opRead ∧ Cont A K scopeRead ∧
              Cont scopeRead S replayRead ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := ⟨replayRead, hsame_refl replayRead, replayUnary⟩
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
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, opRoute, scopeRoute, replayRoute, provenancePkg⟩
  }
  exact ⟨cert, opUnary, scopeUnary, replayUnary⟩

end BEDC.Derived.PredictiveDescentUp
