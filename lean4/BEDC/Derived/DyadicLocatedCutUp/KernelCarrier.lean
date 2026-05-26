import BEDC.Derived.DyadicLocatedCutUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DyadicLocatedCutUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DyadicLocatedCutCarrier [AskSetup] [PackageSetup]
    (lower upper gap window readback sealRow transport replay provenance localCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory gap ∧ UnaryHistory window ∧
    UnaryHistory readback ∧ UnaryHistory sealRow ∧ UnaryHistory transport ∧
      UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory localCert ∧
        Cont lower upper gap ∧ Cont gap window readback ∧ Cont readback sealRow localCert ∧
          Cont transport replay provenance ∧ PkgSig bundle provenance pkg ∧
            PkgSig bundle localCert pkg

theorem DyadicLocatedCutCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {lower upper gap window readback sealRow transport replay provenance localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicLocatedCutCarrier lower upper gap window readback sealRow transport replay provenance
        localCert bundle pkg ->
      SemanticNameCert
          (fun row : BHist => hsame row localCert ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row lower ∨ hsame row upper ∨ hsame row gap ∨ hsame row window ∨
              hsame row readback ∨ hsame row sealRow ∨ hsame row localCert)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle localCert pkg ∧
              hsame row localCert)
          hsame ∧
        Cont lower upper gap ∧ Cont gap window readback ∧ Cont readback sealRow localCert ∧
          PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle Pkg SemanticNameCert UnaryHistory
  intro carrier
  obtain ⟨_lowerUnary, _upperUnary, _gapUnary, _windowUnary, _readbackUnary, _sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, localCertUnary, lowerUpperGap,
    gapWindowReadback, readbackSealLocalCert, _transportReplayProvenance, provenancePkg,
    localCertPkg⟩ := carrier
  have sourceLocalCert :
      (fun row : BHist => hsame row localCert ∧ UnaryHistory row) localCert :=
    ⟨hsame_refl localCert, localCertUnary⟩
  have core :
      NameCert (fun row : BHist => hsame row localCert ∧ UnaryHistory row) hsame := {
    carrier_inhabited := Exists.intro localCert sourceLocalCert
    equiv_refl := by
      intro row _source
      exact hsame_refl row
    equiv_symm := by
      intro _row _row' sameRows
      exact hsame_symm sameRows
    equiv_trans := by
      intro _row _row' _row'' sameLeft sameRight
      exact hsame_trans sameLeft sameRight
    carrier_respects_equiv := by
      intro _row row' sameRows source
      exact
        ⟨hsame_trans (hsame_symm sameRows) source.left,
          unary_transport source.right sameRows⟩
  }
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row localCert ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row lower ∨ hsame row upper ∨ hsame row gap ∨ hsame row window ∨
              hsame row readback ∨ hsame row sealRow ∨ hsame row localCert)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle localCert pkg ∧
              hsame row localCert)
          hsame := {
    core := core
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, localCertPkg, source.left⟩
  }
  exact ⟨cert, lowerUpperGap, gapWindowReadback, readbackSealLocalCert, provenancePkg⟩

end BEDC.Derived.DyadicLocatedCutUp
