import BEDC.Derived.HaltingDistinctionUp

namespace BEDC.Derived.HaltingDistinctionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HaltingDistinctionRootDiagonalInscriptionNonescape [AskSetup] [PackageSetup]
    {question trace diagonal halt classifier route provenance cert inscriptionRead
      normalFormRead rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HaltingDistinctionCarrier question trace diagonal halt classifier route provenance cert
        bundle pkg ->
      Cont diagonal trace inscriptionRead ->
        Cont trace route normalFormRead ->
          Cont inscriptionRead normalFormRead rootRead ->
            PkgSig bundle rootRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row rootRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row diagonal ∨ hsame row trace ∨ hsame row inscriptionRead ∨
                      hsame row normalFormRead ∨ hsame row rootRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont diagonal trace inscriptionRead ∧
                      Cont trace route normalFormRead ∧
                        Cont inscriptionRead normalFormRead rootRead ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle rootRead pkg)
                  hsame ∧
                UnaryHistory inscriptionRead ∧ UnaryHistory normalFormRead ∧
                  UnaryHistory rootRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier inscriptionRoute normalFormRoute rootRoute rootPkg
  obtain ⟨_questionUnary, traceUnary, diagonalUnary, _haltUnary, _classifierUnary,
    routeUnary, _provenanceUnary, _certUnary, _questionTraceDiagonal,
    _diagonalHaltClassifier, _classifierRouteCert, provenancePkg⟩ := carrier
  have inscriptionUnary : UnaryHistory inscriptionRead :=
    unary_cont_closed diagonalUnary traceUnary inscriptionRoute
  have normalFormUnary : UnaryHistory normalFormRead :=
    unary_cont_closed traceUnary routeUnary normalFormRoute
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed inscriptionUnary normalFormUnary rootRoute
  have sourceAtRoot : hsame rootRead rootRead ∧ UnaryHistory rootRead :=
    ⟨hsame_refl rootRead, rootUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row rootRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row diagonal ∨ hsame row trace ∨ hsame row inscriptionRead ∨
              hsame row normalFormRead ∨ hsame row rootRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont diagonal trace inscriptionRead ∧
              Cont trace route normalFormRead ∧ Cont inscriptionRead normalFormRead rootRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle rootRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro rootRead sourceAtRoot
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
      exact
        ⟨source.right, inscriptionRoute, normalFormRoute, rootRoute, provenancePkg, rootPkg⟩
  }
  exact ⟨cert, inscriptionUnary, normalFormUnary, rootUnary⟩

end BEDC.Derived.HaltingDistinctionUp
