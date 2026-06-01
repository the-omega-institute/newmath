import BEDC.Derived.PseudometricUp

namespace BEDC.Derived.PseudometricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PseudometricCarrier_triangle_separated_reflection_compatibility
    [AskSetup] [PackageSetup]
    {point distance dyadic stream readback sealRow zeroRow transport replay localName triangleRead
      zeroRead reflectionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PseudometricCarrier point distance dyadic stream readback sealRow zeroRow transport replay
        localName bundle pkg ->
      hsame triangleRead dyadic ->
        Cont stream readback zeroRead ->
          Cont zeroRead sealRow reflectionRead ->
            PkgSig bundle reflectionRead pkg ->
              UnaryHistory triangleRead ∧ UnaryHistory zeroRead ∧
                UnaryHistory reflectionRead ∧ Cont stream readback dyadic ∧
                  Cont dyadic sealRow zeroRow ∧ hsame localName zeroRow ∧
                    PkgSig bundle localName pkg ∧ PkgSig bundle reflectionRead pkg := by
  -- BEDC touchpoint anchor: PseudometricCarrier BHist hsame Cont ProbeBundle PkgSig
  intro carrier triangleDyadic zeroRoute reflectionRoute reflectionPkg
  obtain ⟨_pointUnary, _distanceUnary, dyadicUnary, streamUnary, readbackUnary,
    sealUnary, _zeroUnary, _transportUnary, _replayUnary, _localNameUnary,
    streamReadbackDyadic, dyadicSealZero, localNameZero, localNamePkg⟩ := carrier
  have triangleUnary : UnaryHistory triangleRead :=
    unary_transport dyadicUnary (hsame_symm triangleDyadic)
  have zeroUnary : UnaryHistory zeroRead :=
    unary_cont_closed streamUnary readbackUnary zeroRoute
  have reflectionUnary : UnaryHistory reflectionRead :=
    unary_cont_closed zeroUnary sealUnary reflectionRoute
  exact
    ⟨triangleUnary, zeroUnary, reflectionUnary, streamReadbackDyadic, dyadicSealZero,
      localNameZero, localNamePkg, reflectionPkg⟩

end BEDC.Derived.PseudometricUp
