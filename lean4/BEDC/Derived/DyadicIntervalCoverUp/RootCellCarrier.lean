import BEDC.Derived.DyadicIntervalCoverUp.RootWindowCoverage

namespace BEDC.Derived.DyadicIntervalCoverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicIntervalCoverRootCellCarrier [AskSetup] [PackageSetup]
    {L U M R V W Q A H C P N cellRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicIntervalCoverRootObligationSurface L U M R V W Q A H C P N bundle pkg ->
      Cont L U cellRead ->
        Cont cellRead N namedRead ->
          PkgSig bundle namedRead pkg ->
            UnaryHistory cellRead ∧ UnaryHistory namedRead ∧
              SemanticNameCert
                (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row L ∨ hsame row U ∨ hsame row M ∨ hsame row R ∨
                    hsame row V ∨ hsame row cellRead ∨ hsame row N ∨
                      hsame row namedRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont L U cellRead ∧ Cont cellRead N namedRead ∧
                    PkgSig bundle namedRead pkg)
                hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro surface cellRoute namedRoute namedPkg
  have lUnary : UnaryHistory L := surface.left
  have uUnary : UnaryHistory U := surface.right.left
  have nUnary : UnaryHistory N :=
    surface.right.right.right.right.right.right.right.right.right.right.right.left
  have cellUnary : UnaryHistory cellRead :=
    unary_cont_closed lUnary uUnary cellRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed cellUnary nUnary namedRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row L ∨ hsame row U ∨ hsame row M ∨ hsame row R ∨ hsame row V ∨
            hsame row cellRead ∨ hsame row N ∨ hsame row namedRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont L U cellRead ∧ Cont cellRead N namedRead ∧
            PkgSig bundle namedRead pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, cellRoute, namedRoute, namedPkg⟩
  }
  exact ⟨cellUnary, namedUnary, cert⟩

end BEDC.Derived.DyadicIntervalCoverUp
