import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ArzelaAscoliFiniteModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ArzelaAscoliFiniteModulusCarrier [AskSetup] [PackageSetup]
    (compactSource family modulus windows readback sealRow transport replay provenance
      nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  UnaryHistory compactSource ∧ UnaryHistory family ∧ UnaryHistory modulus ∧
    UnaryHistory windows ∧ UnaryHistory readback ∧ UnaryHistory sealRow ∧
      UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
        Cont compactSource modulus windows ∧ Cont windows readback sealRow ∧
          PkgSig bundle nameRow pkg

theorem ArzelaAscoliFiniteModulusNamecertObligations [AskSetup] [PackageSetup]
    {compactSource family modulus windows readback sealRow transport replay provenance
      nameRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ArzelaAscoliFiniteModulusCarrier compactSource family modulus windows readback sealRow
        transport replay provenance nameRow bundle pkg ->
      SemanticNameCert
          (fun row : BHist => hsame row sealRow ∧ UnaryHistory row)
          (fun row : BHist => hsame row sealRow ∧ Cont compactSource modulus windows)
          (fun row : BHist =>
            hsame row sealRow ∧ Cont windows readback sealRow ∧ PkgSig bundle nameRow pkg)
          hsame ∧
        UnaryHistory windows ∧ UnaryHistory sealRow ∧ PkgSig bundle nameRow pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier
  obtain ⟨compactUnary, _familyUnary, modulusUnary, windowsUnary, readbackUnary,
    sealUnary, _transportUnary, _replayUnary, _provenanceUnary,
    compactModulusWindows, windowsReadbackSeal, namePkg⟩ := carrier
  have _windowsUnaryFromRoute : UnaryHistory windows :=
    unary_cont_closed compactUnary modulusUnary compactModulusWindows
  have _sealUnaryFromRoute : UnaryHistory sealRow :=
    unary_cont_closed windowsUnary readbackUnary windowsReadbackSeal
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRow ∧ UnaryHistory row)
          (fun row : BHist => hsame row sealRow ∧ Cont compactSource modulus windows)
          (fun row : BHist =>
            hsame row sealRow ∧ Cont windows readback sealRow ∧ PkgSig bundle nameRow pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRow ⟨hsame_refl sealRow, sealUnary⟩
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
      exact ⟨source.left, compactModulusWindows⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, windowsReadbackSeal, namePkg⟩
  }
  exact ⟨cert, windowsUnary, sealUnary, namePkg⟩

end BEDC.Derived.ArzelaAscoliFiniteModulusUp
