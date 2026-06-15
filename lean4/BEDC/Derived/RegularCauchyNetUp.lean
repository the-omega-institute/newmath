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

def RegularCauchyNetUp [AskSetup] [PackageSetup]
    (directed tail window readback sealRow transport replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory directed ∧ UnaryHistory tail ∧ UnaryHistory window ∧
    UnaryHistory readback ∧ UnaryHistory sealRow ∧ UnaryHistory transport ∧
      UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
        Cont directed tail window ∧ Cont window readback sealRow ∧
          PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg

namespace RegularCauchyNetUp

theorem RegularCauchyNetCarrier_tail_stability [AskSetup] [PackageSetup]
    {directed tail window readback sealRow transport replay provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.RegularCauchyNetUp directed tail window readback sealRow transport replay
        provenance localName bundle pkg ->
      UnaryHistory directed ∧ UnaryHistory tail ∧ UnaryHistory window ∧ UnaryHistory readback ∧
        UnaryHistory sealRow ∧ Cont directed tail window ∧ Cont window readback sealRow ∧
          PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig
  intro carrier
  obtain ⟨directedUnary, tailUnary, windowUnary, readbackUnary, sealUnary, _transportUnary,
    _replayUnary, _provenanceUnary, _localNameUnary, directedTailWindow,
    windowReadbackSeal, provenancePkg, localNamePkg⟩ := carrier
  exact
    ⟨directedUnary, tailUnary, windowUnary, readbackUnary, sealUnary,
      directedTailWindow, windowReadbackSeal, provenancePkg, localNamePkg⟩

end RegularCauchyNetUp
end BEDC.Derived
