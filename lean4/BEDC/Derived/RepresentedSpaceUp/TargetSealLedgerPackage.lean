import BEDC.Derived.RepresentedSpaceUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.RepresentedSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RepresentedSpaceTargetSealLedgerPackage [AskSetup] [PackageSetup]
    {name schedule relation target transport replay provenance localName targetSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.RepresentedSpaceUp name schedule relation target transport replay provenance
        localName bundle pkg ->
      Cont target provenance targetSeal ->
        PkgSig bundle targetSeal pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row targetSeal ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row target ∨ hsame row provenance ∨ hsame row transport ∨
                  hsame row targetSeal)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle targetSeal pkg)
              hsame ∧
            UnaryHistory targetSeal ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier targetProvenanceSeal targetSealPkg
  obtain ⟨_nameUnary, _scheduleUnary, _relationUnary, targetUnary, _transportUnary,
    _replayUnary, provenanceUnary, _localNameUnary, _nameScheduleReplay,
    _relationTargetTransport, _localNameTransport, provenancePkg⟩ := carrier
  have targetSealUnary : UnaryHistory targetSeal :=
    unary_cont_closed targetUnary provenanceUnary targetProvenanceSeal
  have sourceTargetSeal :
      (fun row : BHist => hsame row targetSeal ∧ UnaryHistory row) targetSeal := by
    exact ⟨hsame_refl targetSeal, targetSealUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row targetSeal ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row target ∨ hsame row provenance ∨ hsame row transport ∨
              hsame row targetSeal)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle targetSeal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro targetSeal sourceTargetSeal
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
      exact ⟨source.right, provenancePkg, targetSealPkg⟩
  }
  exact ⟨cert, targetSealUnary, provenancePkg⟩

end BEDC.Derived.RepresentedSpaceUp
