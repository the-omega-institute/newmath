import BEDC.Derived.LocatedOpenUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.LocatedOpenUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocatedOpenObligationSurface [AskSetup] [PackageSetup]
    {locatedCut locatedReal stream regular membership sealRow classifierRow transport replay
      provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedOpenCarrier locatedCut locatedReal stream regular membership sealRow classifierRow transport
      replay provenance localName bundle pkg →
      SemanticNameCert
          (fun row : BHist => hsame row membership ∧ UnaryHistory row)
          (fun row : BHist =>
              hsame row locatedCut ∨ hsame row locatedReal ∨ hsame row stream ∨
                hsame row regular ∨ hsame row membership ∨ hsame row sealRow)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame ∧
        UnaryHistory locatedCut ∧ UnaryHistory locatedReal ∧ UnaryHistory membership ∧
          PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg PkgSig SemanticNameCert hsame
  intro carrier
  obtain ⟨locatedCutUnary, locatedRealUnary, _streamUnary, _regularUnary, membershipUnary,
    _sealUnary, _classifierUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, provenancePkg, localNamePkg⟩ := carrier
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row membership ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row locatedCut ∨ hsame row locatedReal ∨ hsame row stream ∨
              hsame row regular ∨ hsame row membership ∨ hsame row sealRow)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro membership ⟨hsame_refl membership, membershipUnary⟩
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
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left))))
      ledger_sound := by
        intro _row source
        exact ⟨source.right, provenancePkg, localNamePkg⟩
    }
  exact ⟨cert, locatedCutUnary, locatedRealUnary, membershipUnary, provenancePkg⟩

end BEDC.Derived.LocatedOpenUp
