import BEDC.Derived.RealCauchyModulusUp.TasteGate

namespace BEDC.Derived.RealCauchyModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealCauchyModulusCarrier_finite_modulus_index_induction [AskSetup] [PackageSetup]
    {modulus windows dyadic readback sealRow transports routes provenance localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCauchyModulusCarrier modulus windows dyadic readback sealRow transports routes provenance
        localCert bundle pkg ->
      forall indexWindow : BHist, UnaryHistory indexWindow ->
        exists familyTail familyDyadic familySeal : BHist,
          Cont windows indexWindow familyTail ∧ Cont familyTail dyadic familyDyadic ∧
            Cont familyDyadic readback familySeal ∧ UnaryHistory familyTail ∧
              UnaryHistory familyDyadic ∧ UnaryHistory familySeal ∧
                Cont modulus windows dyadic ∧ Cont dyadic readback sealRow ∧
                  PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier indexWindow indexUnary
  obtain ⟨_modulusUnary, windowsUnary, dyadicUnary, readbackUnary, _sealUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _localCertUnary, modulusWindowsDyadic,
      dyadicReadbackSeal, _sealRoutesProvenance, provenancePkg, _localSemantic⟩ := carrier
  let familyTail : BHist := append windows indexWindow
  let familyDyadic : BHist := append familyTail dyadic
  let familySeal : BHist := append familyDyadic readback
  have familyTailCont : Cont windows indexWindow familyTail := rfl
  have familyTailUnary : UnaryHistory familyTail :=
    unary_cont_closed windowsUnary indexUnary familyTailCont
  have familyDyadicCont : Cont familyTail dyadic familyDyadic := rfl
  have familyDyadicUnary : UnaryHistory familyDyadic :=
    unary_cont_closed familyTailUnary dyadicUnary familyDyadicCont
  have familySealCont : Cont familyDyadic readback familySeal := rfl
  have familySealUnary : UnaryHistory familySeal :=
    unary_cont_closed familyDyadicUnary readbackUnary familySealCont
  exact
    ⟨familyTail, familyDyadic, familySeal, familyTailCont, familyDyadicCont,
      familySealCont, familyTailUnary, familyDyadicUnary, familySealUnary,
      modulusWindowsDyadic, dyadicReadbackSeal, provenancePkg⟩

end BEDC.Derived.RealCauchyModulusUp
