import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
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

end UniformCauchyCompletionRealizerUp
end BEDC.Derived
