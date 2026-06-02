import BEDC.Derived.MetaCICDecidableBoundaryUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.MetaCICDecidableBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def MetaCICDecidableBoundaryCarrier [AskSetup] [PackageSetup]
    (checker structural bounded finished refusal transport replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory checker ∧ UnaryHistory structural ∧ UnaryHistory finished ∧
    UnaryHistory refusal ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
      UnaryHistory provenance ∧ UnaryHistory localName ∧
        Cont checker structural bounded ∧ PkgSig bundle provenance pkg ∧
          PkgSig bundle localName pkg

theorem MetaCICDecidableBoundary_sibling_provenance [AskSetup] [PackageSetup]
    {checker structural bounded finished refusal transport replay provenance localName
      siblingRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICDecidableBoundaryCarrier checker structural bounded finished refusal transport replay
        provenance localName bundle pkg →
      Cont provenance replay siblingRead →
        PkgSig bundle siblingRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row siblingRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row provenance ∨ hsame row siblingRead ∨
                  Cont provenance replay siblingRead)
              (fun _ : BHist => PkgSig bundle provenance pkg ∧ PkgSig bundle siblingRead pkg)
              hsame ∧
            UnaryHistory siblingRead := by
  -- BEDC touchpoint anchor: MetaCICDecidableBoundaryCarrier BHist Cont ProbeBundle PkgSig SemanticNameCert
  intro carrier provenanceReplaySibling siblingPkg
  obtain ⟨_checkerUnary, _structuralUnary, _finishedUnary, _refusalUnary, _transportUnary,
    replayUnary, provenanceUnary, _localNameUnary, _checkerStructuralBounded,
    provenancePkg, _localNamePkg⟩ := carrier
  have siblingUnary : UnaryHistory siblingRead :=
    unary_cont_closed provenanceUnary replayUnary provenanceReplaySibling
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row siblingRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row provenance ∨ hsame row siblingRead ∨
              Cont provenance replay siblingRead)
          (fun row : BHist => PkgSig bundle provenance pkg ∧ PkgSig bundle siblingRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro siblingRead ⟨hsame_refl siblingRead, siblingUnary⟩
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
      exact Or.inr (Or.inl source.left)
    ledger_sound := by
      intro _ _source
      exact ⟨provenancePkg, siblingPkg⟩
  }
  exact ⟨cert, siblingUnary⟩

end BEDC.Derived.MetaCICDecidableBoundaryUp
