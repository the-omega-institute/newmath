import BEDC.Derived.RealUniformStructureUp

namespace BEDC.Derived.RealUniformStructureUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealUniformStructureSubbasisCompletionHandoff [AskSetup] [PackageSetup]
    {R M U F D S Q H C P N subbasisRead completionRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealUniformStructureCarrier R M U F D S Q H C P N bundle pkg →
      Cont U F subbasisRead →
        Cont subbasisRead C completionRead →
          Cont completionRead N namedRead →
            PkgSig bundle namedRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row U ∨ hsame row F ∨ hsame row C ∨ hsame row N ∨
                      hsame row namedRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont U F subbasisRead ∧
                      Cont subbasisRead C completionRead ∧
                        Cont completionRead N namedRead ∧ PkgSig bundle namedRead pkg)
                  hsame ∧ UnaryHistory subbasisRead ∧ UnaryHistory completionRead ∧
                UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: RealUniformStructureCarrier BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier subbasisRoute completionRoute namedRoute namedPkg
  have uUnary : UnaryHistory U := carrier.right.right.left
  have fUnary : UnaryHistory F := carrier.right.right.right.left
  have cUnary : UnaryHistory C := carrier.right.right.right.right.right.right.right.right.left
  have nUnary : UnaryHistory N := carrier.right.right.right.right.right.right.right.right.right.right.left
  have subbasisUnary : UnaryHistory subbasisRead :=
    unary_cont_closed uUnary fUnary subbasisRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed subbasisUnary cUnary completionRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed completionUnary nUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row U ∨ hsame row F ∨ hsame row C ∨ hsame row N ∨
              hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont U F subbasisRead ∧
              Cont subbasisRead C completionRead ∧ Cont completionRead N namedRead ∧
                PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
      exact ⟨source.right, subbasisRoute, completionRoute, namedRoute, namedPkg⟩
  }
  exact ⟨cert, subbasisUnary, completionUnary, namedUnary⟩

end BEDC.Derived.RealUniformStructureUp
