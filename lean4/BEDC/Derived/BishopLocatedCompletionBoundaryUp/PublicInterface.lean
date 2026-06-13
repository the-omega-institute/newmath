import BEDC.Derived.BishopLocatedCompletionBoundaryUp.RegularCauchyExtraction

namespace BEDC.Derived.BishopLocatedCompletionBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BishopLocatedCompletionBoundaryPublicInterface [AskSetup] [PackageSetup]
    {S Q D R L E T H C P N terminalRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BishopLocatedCompletionBoundaryCarrier S Q D R L E T H C P N bundle pkg →
      Cont E T terminalRead →
        Cont terminalRead N publicRead →
          PkgSig bundle publicRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row S ∨ hsame row Q ∨ hsame row D ∨ hsame row R ∨
                    hsame row L ∨ hsame row E ∨ hsame row T ∨ hsame row publicRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont E T terminalRead ∧
                    Cont terminalRead N publicRead ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle publicRead pkg)
                hsame ∧
              UnaryHistory terminalRead ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BishopLocatedCompletionBoundaryCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier terminalRoute publicRoute publicPkg
  obtain ⟨sUnary, qUnary, dUnary, rUnary, lUnary, eUnary, tUnary, _hUnary, _cUnary,
    _pUnary, nUnary, _streamRegseqDyadic, _dyadicRegularLocated,
    _locatedRealSeal, provenancePkg, _localNamePkg⟩ := carrier
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed eUnary tUnary terminalRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed terminalUnary nUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row Q ∨ hsame row D ∨ hsame row R ∨ hsame row L ∨
              hsame row E ∨ hsame row T ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont E T terminalRead ∧ Cont terminalRead N publicRead ∧
              PkgSig bundle P pkg ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, terminalRoute, publicRoute, provenancePkg, publicPkg⟩
  }
  exact ⟨cert, terminalUnary, publicUnary⟩

end BEDC.Derived.BishopLocatedCompletionBoundaryUp
