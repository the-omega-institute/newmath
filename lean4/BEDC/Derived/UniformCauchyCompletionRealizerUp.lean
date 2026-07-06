import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def UniformCauchyCompletionRealizerUp [AskSetup] [PackageSetup]
    (source dyadic window readback modulus sealRow transport replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory dyadic ∧ UnaryHistory window ∧
    UnaryHistory readback ∧ UnaryHistory modulus ∧ UnaryHistory sealRow ∧
      UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
        UnaryHistory localName ∧ Cont source dyadic window ∧ Cont window readback modulus ∧
          Cont readback modulus sealRow ∧ PkgSig bundle provenance pkg ∧
            PkgSig bundle localName pkg

namespace UniformCauchyCompletionRealizerUp

theorem UniformCauchyCompletionRealizerCarrier_real_seal_handoff [AskSetup] [PackageSetup]
    {source dyadic window readback modulus sealRow transport replay provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.UniformCauchyCompletionRealizerUp source dyadic window readback modulus sealRow
        transport replay provenance localName bundle pkg ->
      UnaryHistory source ∧ UnaryHistory dyadic ∧ UnaryHistory window ∧
        UnaryHistory readback ∧ UnaryHistory modulus ∧ UnaryHistory sealRow ∧
          Cont source dyadic window ∧ Cont window readback modulus ∧
            Cont readback modulus sealRow ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier
  obtain ⟨sourceUnary, dyadicUnary, windowUnary, readbackUnary, modulusUnary, sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary, sourceDyadicWindow,
    windowReadbackModulus, readbackModulusSeal, provenancePkg, localNamePkg⟩ := carrier
  exact
    ⟨sourceUnary, dyadicUnary, windowUnary, readbackUnary, modulusUnary, sealUnary,
      sourceDyadicWindow, windowReadbackModulus, readbackModulusSeal, provenancePkg,
      localNamePkg⟩

theorem UniformCauchyCompletionRealizer_namecert_obligations [AskSetup] [PackageSetup]
    {source dyadic window readback modulus sealRow transport replay provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.UniformCauchyCompletionRealizerUp source dyadic window readback modulus sealRow
        transport replay provenance localName bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          BEDC.Derived.UniformCauchyCompletionRealizerUp source dyadic window readback modulus
            sealRow transport replay provenance localName bundle pkg ∧ hsame row localName)
        (fun row : BHist =>
          BEDC.Derived.UniformCauchyCompletionRealizerUp source dyadic window readback modulus
            sealRow transport replay provenance localName bundle pkg ∧ hsame row localName)
        (fun row : BHist =>
          BEDC.Derived.UniformCauchyCompletionRealizerUp source dyadic window readback modulus
            sealRow transport replay provenance localName bundle pkg ∧ hsame row localName)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro localName ⟨carrier, hsame_refl localName⟩
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
        have sameOtherRow : hsame _other _row := hsame_symm sameRows
        exact ⟨source.left, hsame_trans sameOtherRow source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

end UniformCauchyCompletionRealizerUp
end BEDC.Derived
