import BEDC.Derived.DiagonalCofinalTailUp

namespace BEDC.Derived.DiagonalCofinalTailUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalCofinalTailCarrier_nonescape [AskSetup] [PackageSetup]
    {q s g d r w h c p n observation terminalRead completionConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalCofinalTailCarrier q s g d r w h c p n bundle pkg →
      Cont g d observation →
        Cont r w terminalRead →
          Cont terminalRead c completionConsumer →
            PkgSig bundle completionConsumer pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    (hsame row observation ∨ hsame row terminalRead ∨
                      hsame row completionConsumer) ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row q ∨ hsame row s ∨ hsame row g ∨ hsame row d ∨
                      hsame row r ∨ hsame row w ∨ hsame row observation ∨
                        hsame row terminalRead ∨ hsame row completionConsumer)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont g d observation ∧ Cont r w terminalRead ∧
                      Cont terminalRead c completionConsumer ∧
                        PkgSig bundle completionConsumer pkg)
                  hsame ∧
                UnaryHistory observation ∧ UnaryHistory terminalRead ∧
                  UnaryHistory completionConsumer ∧ PkgSig bundle p pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier observationRoute terminalRoute completionRoute completionPkg
  obtain ⟨_qUnary, _sUnary, gUnary, dUnary, rUnary, wUnary, _hUnary, cUnary,
    _pUnary, _nUnary, _qsRoute, _gdRoute, _whRoute, pPkg⟩ := carrier
  have observationUnary : UnaryHistory observation :=
    unary_cont_closed gUnary dUnary observationRoute
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed rUnary wUnary terminalRoute
  have completionUnary : UnaryHistory completionConsumer :=
    unary_cont_closed terminalUnary cUnary completionRoute
  have sourceCompletion :
      (fun row : BHist =>
        (hsame row observation ∨ hsame row terminalRead ∨
          hsame row completionConsumer) ∧ UnaryHistory row) completionConsumer := by
    exact ⟨Or.inr (Or.inr (hsame_refl completionConsumer)), completionUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row observation ∨ hsame row terminalRead ∨
              hsame row completionConsumer) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row q ∨ hsame row s ∨ hsame row g ∨ hsame row d ∨ hsame row r ∨
              hsame row w ∨ hsame row observation ∨ hsame row terminalRead ∨
                hsame row completionConsumer)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont g d observation ∧ Cont r w terminalRead ∧
              Cont terminalRead c completionConsumer ∧ PkgSig bundle completionConsumer pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro completionConsumer sourceCompletion
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
        constructor
        · cases source.left with
          | inl sameObservation =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameObservation)
          | inr rest =>
              cases rest with
              | inl sameTerminal =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameTerminal))
              | inr sameCompletion =>
                  exact
                    Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameCompletion))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameObservation =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameObservation))))))
      | inr rest =>
          cases rest with
          | inl sameTerminal =>
              exact
                Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inr (Or.inl sameTerminal)))))))
          | inr sameCompletion =>
              exact
                Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inr (Or.inr sameCompletion)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, observationRoute, terminalRoute, completionRoute, completionPkg⟩
  }
  exact ⟨cert, observationUnary, terminalUnary, completionUnary, pPkg⟩

end BEDC.Derived.DiagonalCofinalTailUp
