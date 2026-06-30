import BEDC.Derived.KleeneTreeUp.NameCertObligations

namespace BEDC.Derived.KleeneTreeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem KleeneTreeCantorSpaceFanBoundary [AskSetup] [PackageSetup]
    {tree cantor fan _transport route provenance _cert boundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory tree ->
      UnaryHistory cantor ->
        UnaryHistory fan ->
          Cont tree cantor boundary ->
            Cont boundary fan route ->
              PkgSig bundle provenance pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row boundary ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row tree ∨ hsame row cantor ∨ hsame row fan ∨
                        hsame row boundary)
                    (fun row : BHist =>
                      hsame row boundary ∧ Cont tree cantor boundary ∧
                        Cont boundary fan route ∧ PkgSig bundle provenance pkg)
                    hsame ∧
                  UnaryHistory boundary ∧ UnaryHistory route ∧
                    Cont tree cantor boundary ∧ Cont boundary fan route ∧
                      PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro treeUnary cantorUnary fanUnary boundaryRoute fanRoute provenancePkg
  have boundaryUnary : UnaryHistory boundary :=
    unary_cont_closed treeUnary cantorUnary boundaryRoute
  have routeUnary : UnaryHistory route :=
    unary_cont_closed boundaryUnary fanUnary fanRoute
  have certObj :
      SemanticNameCert
          (fun row : BHist => hsame row boundary ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row tree ∨ hsame row cantor ∨ hsame row fan ∨ hsame row boundary)
          (fun row : BHist =>
            hsame row boundary ∧ Cont tree cantor boundary ∧ Cont boundary fan route ∧
              PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro boundary ⟨hsame_refl boundary, boundaryUnary⟩
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
      exact Or.inr (Or.inr (Or.inr source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, boundaryRoute, fanRoute, provenancePkg⟩
  }
  exact ⟨certObj, boundaryUnary, routeUnary, boundaryRoute, fanRoute, provenancePkg⟩

end BEDC.Derived.KleeneTreeUp
