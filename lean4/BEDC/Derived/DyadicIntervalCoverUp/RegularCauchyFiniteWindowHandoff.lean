import BEDC.Derived.DyadicIntervalCoverUp.RootWindowCoverage

namespace BEDC.Derived.DyadicIntervalCoverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicIntervalCoverRegularCauchyFiniteWindowHandoff [AskSetup] [PackageSetup]
    {L U M R V W Q A H C P N regularWindow publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicIntervalCoverRootObligationSurface L U M R V W Q A H C P N bundle pkg →
      Cont R W regularWindow →
        Cont regularWindow A publicRead →
          PkgSig bundle P pkg →
            PkgSig bundle publicRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row R ∨ hsame row W ∨ hsame row A ∨ hsame row regularWindow ∨
                      hsame row publicRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont R W regularWindow ∧
                      Cont regularWindow A publicRead ∧ PkgSig bundle P pkg ∧
                        PkgSig bundle publicRead pkg)
                  hsame ∧ UnaryHistory regularWindow ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: DyadicIntervalCoverRootObligationSurface BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro surface regularRoute publicRoute provenancePkg publicPkg
  have rUnary : UnaryHistory R := surface.right.right.right.left
  have wUnary : UnaryHistory W := surface.right.right.right.right.right.left
  have aUnary : UnaryHistory A :=
    surface.right.right.right.right.right.right.right.left
  have regularWindowUnary : UnaryHistory regularWindow :=
    unary_cont_closed rUnary wUnary regularRoute
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed regularWindowUnary aUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row R ∨ hsame row W ∨ hsame row A ∨ hsame row regularWindow ∨
              hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont R W regularWindow ∧ Cont regularWindow A publicRead ∧
              PkgSig bundle P pkg ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, publicReadUnary⟩
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
      exact ⟨source.right, regularRoute, publicRoute, provenancePkg, publicPkg⟩
  }
  exact ⟨cert, regularWindowUnary, publicReadUnary⟩

end BEDC.Derived.DyadicIntervalCoverUp
