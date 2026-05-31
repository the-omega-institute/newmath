import BEDC.Derived.MetaCICDecidableBoundaryUp.SiblingProvenance

namespace BEDC.Derived.MetaCICDecidableBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICDecidableBoundary_obligation_closure_package [AskSetup] [PackageSetup]
    {checker structural boundedNormal finished refusal transport replay provenance localName
      boundedRead replayRead packageRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICDecidableBoundaryCarrier checker structural boundedNormal finished refusal transport
        replay provenance localName bundle pkg ->
      Cont boundedNormal finished boundedRead ->
        Cont boundedRead replay replayRead ->
          Cont replayRead transport packageRead ->
            PkgSig bundle packageRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row packageRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row checker ∨ hsame row structural ∨ hsame row boundedNormal ∨
                      hsame row finished ∨ hsame row refusal ∨ hsame row packageRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont checker structural boundedNormal ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle packageRead pkg)
                  hsame ∧
                UnaryHistory boundedNormal ∧ UnaryHistory boundedRead ∧
                  UnaryHistory replayRead ∧ UnaryHistory packageRead := by
  -- BEDC touchpoint anchor: MetaCICDecidableBoundaryCarrier BHist Cont ProbeBundle PkgSig SemanticNameCert
  intro carrier boundedRoute replayRoute packageRoute packagePkg
  obtain ⟨checkerUnary, structuralUnary, finishedUnary, _refusalUnary, transportUnary,
    replayUnary, _provenanceUnary, _localNameUnary, checkerStructuralBounded,
    provenancePkg, _localNamePkg⟩ := carrier
  have boundedNormalUnary : UnaryHistory boundedNormal :=
    unary_cont_closed checkerUnary structuralUnary checkerStructuralBounded
  have boundedReadUnary : UnaryHistory boundedRead :=
    unary_cont_closed boundedNormalUnary finishedUnary boundedRoute
  have replayReadUnary : UnaryHistory replayRead :=
    unary_cont_closed boundedReadUnary replayUnary replayRoute
  have packageReadUnary : UnaryHistory packageRead :=
    unary_cont_closed replayReadUnary transportUnary packageRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row packageRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row checker ∨ hsame row structural ∨ hsame row boundedNormal ∨
              hsame row finished ∨ hsame row refusal ∨ hsame row packageRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont checker structural boundedNormal ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle packageRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro packageRead ⟨hsame_refl packageRead, packageReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, checkerStructuralBounded, provenancePkg, packagePkg⟩
  }
  exact
    ⟨cert, boundedNormalUnary, boundedReadUnary, replayReadUnary, packageReadUnary⟩

end BEDC.Derived.MetaCICDecidableBoundaryUp
