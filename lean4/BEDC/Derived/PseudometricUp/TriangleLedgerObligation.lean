import BEDC.Derived.PseudometricUp

namespace BEDC.Derived.PseudometricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PseudometricCarrier_triangle_ledger_obligation [AskSetup] [PackageSetup]
    {point distance dyadic stream readback sealRow zeroRow transport replay localName
      triangleRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PseudometricCarrier point distance dyadic stream readback sealRow zeroRow transport replay
        localName bundle pkg ->
      hsame triangleRead dyadic ->
        UnaryHistory triangleRead ∧ UnaryHistory dyadic ∧ UnaryHistory stream ∧
          UnaryHistory readback ∧ UnaryHistory sealRow ∧ Cont stream readback dyadic ∧
            Cont dyadic sealRow zeroRow ∧ hsame localName zeroRow ∧
              PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: PseudometricCarrier BHist hsame Cont ProbeBundle Pkg
  intro carrier triangleDyadic
  obtain ⟨_pointUnary, _distanceUnary, dyadicUnary, streamUnary, readbackUnary,
    sealUnary, _zeroUnary, _transportUnary, _replayUnary, _localNameUnary,
    streamReadbackDyadic, dyadicSealZero, localNameZero, localNamePkg⟩ := carrier
  have triangleUnary : UnaryHistory triangleRead :=
    unary_transport dyadicUnary (hsame_symm triangleDyadic)
  exact
    ⟨triangleUnary, dyadicUnary, streamUnary, readbackUnary, sealUnary,
      streamReadbackDyadic, dyadicSealZero, localNameZero, localNamePkg⟩

end BEDC.Derived.PseudometricUp
