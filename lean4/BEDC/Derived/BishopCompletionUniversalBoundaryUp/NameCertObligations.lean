import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BishopCompletionUniversalBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BishopCompletionUniversalBoundaryCarrier [AskSetup] [PackageSetup]
    (completion windows readback dyadic realSeal universal extension uniqueness transport replay
      provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle PkgSig SemanticNameCert UnaryHistory
  UnaryHistory completion ∧ UnaryHistory windows ∧ UnaryHistory readback ∧
    UnaryHistory dyadic ∧ UnaryHistory realSeal ∧ UnaryHistory universal ∧
      UnaryHistory extension ∧ UnaryHistory uniqueness ∧ UnaryHistory transport ∧
        UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
          Cont completion windows readback ∧ Cont readback dyadic realSeal ∧
            Cont universal extension uniqueness ∧ hsame transport transport ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg

theorem BishopCompletionUniversalBoundaryCarrier_namecert_obligations
    [AskSetup] [PackageSetup]
    {completion windows readback dyadic realSeal universal extension uniqueness transport replay
      provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BishopCompletionUniversalBoundaryCarrier completion windows readback dyadic realSeal
        universal extension uniqueness transport replay provenance localName bundle pkg →
      SemanticNameCert
          (fun row : BHist =>
            hsame row extension ∧
              BishopCompletionUniversalBoundaryCarrier completion windows readback dyadic
                realSeal universal extension uniqueness transport replay provenance localName
                bundle pkg)
          (fun row : BHist => hsame row extension ∧ Cont universal extension uniqueness)
          (fun row : BHist => hsame row extension ∧ PkgSig bundle provenance pkg)
          hsame ∧
        UnaryHistory completion ∧ UnaryHistory windows ∧ UnaryHistory readback ∧
          UnaryHistory dyadic ∧ UnaryHistory realSeal ∧ UnaryHistory universal ∧
            UnaryHistory extension ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle PkgSig SemanticNameCert UnaryHistory
  intro carrier
  have carrierWitness := carrier
  obtain ⟨completionUnary, windowsUnary, readbackUnary, dyadicUnary, realSealUnary,
    universalUnary, extensionUnary, _uniquenessUnary, _transportUnary, _replayUnary,
    _provenanceUnary, _localNameUnary, _completionRoute, _realSealRoute, extensionRoute,
    _transportSame, provenancePkg, _localNamePkg⟩ := carrier
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row extension ∧
            BishopCompletionUniversalBoundaryCarrier completion windows readback dyadic
              realSeal universal extension uniqueness transport replay provenance localName
              bundle pkg)
        (fun row : BHist => hsame row extension ∧ Cont universal extension uniqueness)
        (fun row : BHist => hsame row extension ∧ PkgSig bundle provenance pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro extension ⟨hsame_refl extension, carrierWitness⟩
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
      exact ⟨source.left, extensionRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, provenancePkg⟩
  }
  exact
    ⟨cert, completionUnary, windowsUnary, readbackUnary, dyadicUnary, realSealUnary,
      universalUnary, extensionUnary, provenancePkg⟩

end BEDC.Derived.BishopCompletionUniversalBoundaryUp
