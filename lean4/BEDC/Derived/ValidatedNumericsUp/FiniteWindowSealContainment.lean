import BEDC.Derived.ValidatedNumericsUp

namespace BEDC.Derived.ValidatedNumericsUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ValidatedNumericsPacket_finite_window_seal_containment [AskSetup] [PackageSetup]
    {interval precision modulus observation readback transport containment provenance name
      finiteRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ValidatedNumericsPacket interval precision modulus observation readback transport containment
        provenance name bundle pkg ->
      Cont observation readback finiteRead ->
        Cont interval containment sealRead ->
          PkgSig bundle sealRead pkg ->
            UnaryHistory finiteRead ∧ UnaryHistory sealRead ∧
              Cont precision modulus observation ∧ Cont observation readback finiteRead ∧
                Cont interval containment sealRead ∧ PkgSig bundle name pkg ∧
                  PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig
  intro packet observationReadbackFinite intervalContainmentSeal sealPkg
  obtain ⟨intervalUnary, _precisionUnary, _modulusUnary, observationUnary, readbackUnary,
    _transportUnary, containmentUnary, _provenanceUnary, _nameUnary,
    precisionModulusObservation, _observationReadbackTransport,
    _observationIntervalContainment, _containmentProvenanceName, namePkg⟩ := packet
  have finiteReadUnary : UnaryHistory finiteRead :=
    unary_cont_closed observationUnary readbackUnary observationReadbackFinite
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed intervalUnary containmentUnary intervalContainmentSeal
  exact
    ⟨finiteReadUnary, sealReadUnary, precisionModulusObservation, observationReadbackFinite,
      intervalContainmentSeal, namePkg, sealPkg⟩

end BEDC.Derived.ValidatedNumericsUp
