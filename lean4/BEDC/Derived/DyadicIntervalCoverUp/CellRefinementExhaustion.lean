import BEDC.Derived.DyadicIntervalCoverUp.RootWindowCoverage

namespace BEDC.Derived.DyadicIntervalCoverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicIntervalCoverCellRefinementExhaustion [AskSetup] [PackageSetup]
    {L U M R V W Q A H C P N cellRead coverRead sealRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicIntervalCoverRootObligationSurface L U M R V W Q A H C P N bundle pkg →
      Cont L U cellRead →
        Cont M R coverRead →
          Cont coverRead A sealRead →
            Cont cellRead N namedRead →
              PkgSig bundle namedRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row L ∨ hsame row U ∨ hsame row M ∨ hsame row R ∨
                        hsame row V ∨ hsame row W ∨ hsame row Q ∨ hsame row A ∨
                          hsame row cellRead ∨ hsame row coverRead ∨
                            hsame row sealRead ∨ hsame row namedRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont L U cellRead ∧ Cont M R coverRead ∧
                        Cont coverRead A sealRead ∧ Cont cellRead N namedRead ∧
                          PkgSig bundle namedRead pkg)
                    hsame := by
  -- BEDC touchpoint anchor: DyadicIntervalCoverRootObligationSurface BHist Cont PkgSig SemanticNameCert hsame UnaryHistory
  intro surface cellRoute coverRoute sealRoute namedRoute namedPkg
  have lUnary : UnaryHistory L := surface.left
  have uUnary : UnaryHistory U := surface.right.left
  have mUnary : UnaryHistory M := surface.right.right.left
  have rUnary : UnaryHistory R := surface.right.right.right.left
  have aUnary : UnaryHistory A := surface.right.right.right.right.right.right.right.left
  have nUnary : UnaryHistory N :=
    surface.right.right.right.right.right.right.right.right.right.right.right.left
  have cellUnary : UnaryHistory cellRead :=
    unary_cont_closed lUnary uUnary cellRoute
  have coverUnary : UnaryHistory coverRead :=
    unary_cont_closed mUnary rUnary coverRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed coverUnary aUnary sealRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed cellUnary nUnary namedRoute
  exact {
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
      exact ⟨source.right, cellRoute, coverRoute, sealRoute, namedRoute, namedPkg⟩
  }

end BEDC.Derived.DyadicIntervalCoverUp
