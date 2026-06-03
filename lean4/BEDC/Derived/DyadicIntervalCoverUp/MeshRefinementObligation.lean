import BEDC.Derived.DyadicIntervalCoverUp.RootWindowCoverage

namespace BEDC.Derived.DyadicIntervalCoverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicIntervalCoverMeshRefinementObligation [AskSetup] [PackageSetup]
    {L U M R V W Q A H C P N refinedEndpoint refinedCover namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicIntervalCoverRootObligationSurface L U M R V W Q A H C P N bundle pkg →
      Cont L U refinedEndpoint →
        Cont M R refinedCover →
          Cont refinedCover N namedRead →
            PkgSig bundle namedRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row L ∨ hsame row U ∨ hsame row M ∨ hsame row R ∨
                      hsame row V ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                        hsame row N ∨ hsame row namedRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont L U refinedEndpoint ∧
                      Cont M R refinedCover ∧ Cont refinedCover N namedRead ∧
                        PkgSig bundle namedRead pkg)
                  hsame ∧ UnaryHistory refinedEndpoint ∧ UnaryHistory refinedCover ∧
                UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro surface endpointCont coverCont nameCont namePkg
  have lUnary : UnaryHistory L := surface.left
  have uUnary : UnaryHistory U := surface.right.left
  have mUnary : UnaryHistory M := surface.right.right.left
  have rUnary : UnaryHistory R := surface.right.right.right.left
  have nUnary : UnaryHistory N :=
    surface.right.right.right.right.right.right.right.right.right.right.right.left
  have endpointUnary : UnaryHistory refinedEndpoint :=
    unary_cont_closed lUnary uUnary endpointCont
  have coverUnary : UnaryHistory refinedCover :=
    unary_cont_closed mUnary rUnary coverCont
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed coverUnary nUnary nameCont
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row L ∨ hsame row U ∨ hsame row M ∨ hsame row R ∨
              hsame row V ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont L U refinedEndpoint ∧ Cont M R refinedCover ∧
              Cont refinedCover N namedRead ∧ PkgSig bundle namedRead pkg)
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
                        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, endpointCont, coverCont, nameCont, namePkg⟩
  }
  exact ⟨cert, endpointUnary, coverUnary, namedUnary⟩

end BEDC.Derived.DyadicIntervalCoverUp
