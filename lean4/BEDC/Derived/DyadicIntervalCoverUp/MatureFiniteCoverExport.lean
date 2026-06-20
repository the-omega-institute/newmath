import BEDC.Derived.DyadicIntervalCoverUp.RootWindowCoverage

namespace BEDC.Derived.DyadicIntervalCoverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicIntervalCoverMatureFiniteCoverExport [AskSetup] [PackageSetup]
    {L U M R V W Q A H C P N compact uniform bridge matureRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicIntervalCoverRootObligationSurface L U M R V W Q A H C P N bundle pkg ->
      UnaryHistory compact ->
        UnaryHistory uniform ->
          Cont A compact bridge ->
            Cont bridge uniform matureRead ->
              PkgSig bundle P pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row matureRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row L ∨ hsame row U ∨ hsame row M ∨ hsame row R ∨
                        hsame row V ∨ hsame row W ∨ hsame row Q ∨ hsame row A ∨
                          hsame row compact ∨ hsame row uniform ∨ hsame row bridge ∨
                            hsame row matureRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧
                        DyadicIntervalCoverRootObligationSurface L U M R V W Q A H C P N
                          bundle pkg ∧
                          Cont A compact bridge ∧ Cont bridge uniform matureRead ∧
                            PkgSig bundle P pkg)
                    hsame ∧ UnaryHistory bridge ∧ UnaryHistory matureRead := by
  -- BEDC touchpoint anchor: DyadicIntervalCoverRootObligationSurface BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro surface compactUnary uniformUnary bridgeRoute matureRoute routePackage
  have aUnary : UnaryHistory A :=
    surface.right.right.right.right.right.right.right.left
  have bridgeUnary : UnaryHistory bridge :=
    unary_cont_closed aUnary compactUnary bridgeRoute
  have matureUnary : UnaryHistory matureRead :=
    unary_cont_closed bridgeUnary uniformUnary matureRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row matureRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row L ∨ hsame row U ∨ hsame row M ∨ hsame row R ∨ hsame row V ∨
              hsame row W ∨ hsame row Q ∨ hsame row A ∨ hsame row compact ∨
                hsame row uniform ∨ hsame row bridge ∨ hsame row matureRead)
          (fun row : BHist =>
            UnaryHistory row ∧
              DyadicIntervalCoverRootObligationSurface L U M R V W Q A H C P N bundle pkg ∧
                Cont A compact bridge ∧ Cont bridge uniform matureRead ∧
                  PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro matureRead ⟨hsame_refl matureRead, matureUnary⟩
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
      exact ⟨source.right, surface, bridgeRoute, matureRoute, routePackage⟩
  }
  exact ⟨cert, bridgeUnary, matureUnary⟩

end BEDC.Derived.DyadicIntervalCoverUp
