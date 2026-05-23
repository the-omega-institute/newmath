import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyRateLatticeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyRateLatticeCarrier [AskSetup] [PackageSetup]
    (sourceA sourceB meet join dominance windows readback sealRow transport replay provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle PkgSig SemanticNameCert UnaryHistory
  UnaryHistory sourceA ∧ UnaryHistory sourceB ∧ UnaryHistory meet ∧ UnaryHistory join ∧
    UnaryHistory dominance ∧ UnaryHistory windows ∧ UnaryHistory readback ∧ UnaryHistory sealRow ∧
      UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
        UnaryHistory localName ∧ Cont sourceA sourceB meet ∧ Cont meet join dominance ∧
          Cont dominance windows readback ∧ Cont readback sealRow replay ∧
            hsame transport transport ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle localName pkg

theorem CauchyRateLatticeCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {sourceA sourceB meet join dominance windows readback sealRow transport replay provenance
      localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyRateLatticeCarrier sourceA sourceB meet join dominance windows readback sealRow
        transport replay provenance localName bundle pkg →
      SemanticNameCert
          (fun row : BHist =>
            hsame row sealRow ∧
              CauchyRateLatticeCarrier sourceA sourceB meet join dominance windows readback
                sealRow transport replay provenance localName bundle pkg)
          (fun row : BHist => hsame row sealRow ∧ Cont readback sealRow replay)
          (fun row : BHist => hsame row sealRow ∧ PkgSig bundle provenance pkg)
          hsame ∧
        UnaryHistory sourceA ∧ UnaryHistory sourceB ∧ UnaryHistory meet ∧ UnaryHistory join ∧
          UnaryHistory dominance ∧ UnaryHistory windows ∧ UnaryHistory readback ∧
            UnaryHistory sealRow ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle PkgSig SemanticNameCert UnaryHistory
  intro carrier
  have carrierWitness := carrier
  obtain ⟨sourceAUnary, sourceBUnary, meetUnary, joinUnary, dominanceUnary, windowsUnary,
    readbackUnary, sealUnary, _transportUnary, replayUnary, _provenanceUnary, _localNameUnary,
    _sourceMeet, _dominanceRoute, _readbackRoute, readbackSealReplay, _transportSame,
    provenancePkg, _localNamePkg⟩ := carrier
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row sealRow ∧
            CauchyRateLatticeCarrier sourceA sourceB meet join dominance windows readback
                sealRow transport replay provenance localName bundle pkg)
        (fun row : BHist => hsame row sealRow ∧ Cont readback sealRow replay)
        (fun row : BHist => hsame row sealRow ∧ PkgSig bundle provenance pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRow ⟨hsame_refl sealRow, carrierWitness⟩
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
        exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact ⟨source.left, readbackSealReplay⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, provenancePkg⟩
  }
  exact
    ⟨cert, sourceAUnary, sourceBUnary, meetUnary, joinUnary, dominanceUnary, windowsUnary,
      readbackUnary, sealUnary, provenancePkg⟩

end BEDC.Derived.CauchyRateLatticeUp
