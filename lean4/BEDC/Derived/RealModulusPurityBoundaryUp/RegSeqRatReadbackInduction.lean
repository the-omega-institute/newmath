import BEDC.Derived.RealModulusPurityBoundaryUp.ScopeBinding

namespace BEDC.Derived.RealModulusPurityBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealModulusPurityBoundaryRegSeqRatReadbackInduction [AskSetup] [PackageSetup]
    {x : RealModulusPurityBoundaryUp}
    {D S R0 L B H C P N routeRL routeLB predicted consumer readbackStep : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    realModulusPurityBoundaryFields x = [D, S, R0, L, B, H, C, P, N] ->
      Cont D S R0 ->
        Cont R0 L routeRL ->
          Cont routeRL B routeLB ->
            Cont routeLB H predicted ->
              Cont routeLB N consumer ->
                Cont S R0 readbackStep ->
                  UnaryHistory D ->
                    UnaryHistory S ->
                      UnaryHistory L ->
                        UnaryHistory B ->
                          UnaryHistory H ->
                            UnaryHistory N ->
                              PkgSig bundle P pkg ->
                                PkgSig bundle readbackStep pkg ->
                                  SemanticNameCert
                                      (fun row : BHist =>
                                        (hsame row R0 ∨ hsame row L ∨ hsame row B ∨
                                          hsame row readbackStep) ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row D ∨ hsame row S ∨ hsame row R0 ∨
                                          hsame row L ∨ hsame row B ∨ hsame row H ∨
                                            hsame row N ∨ hsame row readbackStep)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧ Cont D S R0 ∧
                                          Cont S R0 readbackStep ∧ PkgSig bundle P pkg ∧
                                            PkgSig bundle readbackStep pkg)
                                      hsame ∧
                                    UnaryHistory readbackStep := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro _fields routeR0 _routeRLCont _routeLBCont _predictedCont _consumerCont
    readbackRoute unaryD unaryS _unaryL _unaryB _unaryH _unaryN provenancePkg readbackPkg
  have unaryR0 : UnaryHistory R0 :=
    unary_cont_closed unaryD unaryS routeR0
  have readbackUnary : UnaryHistory readbackStep :=
    unary_cont_closed unaryS unaryR0 readbackRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row R0 ∨ hsame row L ∨ hsame row B ∨ hsame row readbackStep) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row S ∨ hsame row R0 ∨ hsame row L ∨ hsame row B ∨
              hsame row H ∨ hsame row N ∨ hsame row readbackStep)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D S R0 ∧ Cont S R0 readbackStep ∧
              PkgSig bundle P pkg ∧ PkgSig bundle readbackStep pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro readbackStep
        ⟨Or.inr (Or.inr (Or.inr (hsame_refl readbackStep))), readbackUnary⟩
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
        intro _row other sameRows source
        have otherUnary : UnaryHistory other :=
          unary_transport source.right sameRows
        have otherClassified :
            hsame other R0 ∨ hsame other L ∨ hsame other B ∨
              hsame other readbackStep := by
          cases source.left with
          | inl sameR0 =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameR0)
          | inr rest =>
              cases rest with
              | inl sameL =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameL))
              | inr restTail =>
                  cases restTail with
                  | inl sameB =>
                      exact
                        Or.inr
                          (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameB)))
                  | inr sameReadback =>
                      exact
                        Or.inr
                          (Or.inr
                            (Or.inr (hsame_trans (hsame_symm sameRows) sameReadback)))
        exact ⟨otherClassified, otherUnary⟩
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameR0 =>
          exact Or.inr (Or.inr (Or.inl sameR0))
      | inr rest =>
          cases rest with
          | inl sameL =>
              exact Or.inr (Or.inr (Or.inr (Or.inl sameL)))
          | inr restTail =>
              cases restTail with
              | inl sameB =>
                  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameB))))
              | inr sameReadback =>
                  exact
                    Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr (Or.inr sameReadback))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, routeR0, readbackRoute, provenancePkg, readbackPkg⟩
  }
  exact ⟨cert, readbackUnary⟩

end BEDC.Derived.RealModulusPurityBoundaryUp
