import BEDC.Derived.DyadicIntervalCoverUp.RootWindowCoverage

namespace BEDC.Derived.DyadicIntervalCoverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicIntervalCoverRefinementChainInduction [AskSetup] [PackageSetup]
    {L U M R V W Q A H C P N stageRead ledgerRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    (UnaryHistory L ∧ UnaryHistory U ∧ UnaryHistory M ∧ UnaryHistory R ∧
        UnaryHistory V ∧ UnaryHistory W ∧ UnaryHistory Q ∧ UnaryHistory A ∧
          UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
            PkgSig bundle P pkg) →
      Cont L U stageRead →
        Cont stageRead V ledgerRead →
          Cont ledgerRead N namedRead →
            PkgSig bundle namedRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row L ∨ hsame row U ∨ hsame row M ∨ hsame row R ∨
                      hsame row V ∨ hsame row W ∨ hsame row Q ∨ hsame row A ∨
                        hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                          hsame row stageRead ∨ hsame row ledgerRead ∨
                            hsame row namedRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont L U stageRead ∧
                      Cont stageRead V ledgerRead ∧ Cont ledgerRead N namedRead ∧
                        PkgSig bundle P pkg ∧ PkgSig bundle namedRead pkg)
                  hsame ∧ UnaryHistory stageRead ∧ UnaryHistory ledgerRead ∧
                UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro surface stageRoute ledgerRoute namedRoute namedPkg
  have lUnary : UnaryHistory L := surface.left
  have uUnary : UnaryHistory U := surface.right.left
  have vUnary : UnaryHistory V := surface.right.right.right.right.left
  have nUnary : UnaryHistory N :=
    surface.right.right.right.right.right.right.right.right.right.right.right.left
  have pPkg : PkgSig bundle P pkg :=
    surface.right.right.right.right.right.right.right.right.right.right.right.right
  have stageUnary : UnaryHistory stageRead :=
    unary_cont_closed lUnary uUnary stageRoute
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed stageUnary vUnary ledgerRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed ledgerUnary nUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row L ∨ hsame row U ∨ hsame row M ∨ hsame row R ∨
              hsame row V ∨ hsame row W ∨ hsame row Q ∨ hsame row A ∨
                hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                  hsame row stageRead ∨ hsame row ledgerRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont L U stageRead ∧ Cont stageRead V ledgerRead ∧
              Cont ledgerRead N namedRead ∧ PkgSig bundle P pkg ∧
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
                            (Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr source.left)))))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, stageRoute, ledgerRoute, namedRoute, pPkg, namedPkg⟩
  }
  exact ⟨cert, stageUnary, ledgerUnary, namedUnary⟩

end BEDC.Derived.DyadicIntervalCoverUp
