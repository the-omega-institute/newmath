import BEDC.Derived.RealCauchyModulusUp.TasteGate

namespace BEDC.Derived.RealCauchyModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealCauchyModulusCarrier_regseqrat_seal_admission [AskSetup] [PackageSetup]
    {modulus windows dyadic readback sealRow transports routes provenance localCert
      admission : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCauchyModulusCarrier modulus windows dyadic readback sealRow transports routes provenance
        localCert bundle pkg →
      Cont readback sealRow admission →
        PkgSig bundle admission pkg →
          UnaryHistory readback ∧ UnaryHistory sealRow ∧ UnaryHistory admission ∧
            Cont modulus windows dyadic ∧ Cont dyadic readback sealRow ∧
              Cont readback sealRow admission ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle admission pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier admissionCont admissionPkg
  obtain ⟨_modulusUnary, _windowsUnary, _dyadicUnary, readbackUnary, sealUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _localCertUnary, modulusWindowRoute,
      dyadicReadbackRoute, _sealRoute, provenancePkg, _localSemantic⟩ := carrier
  have admissionUnary : UnaryHistory admission :=
    unary_cont_closed readbackUnary sealUnary admissionCont
  exact
    ⟨readbackUnary, sealUnary, admissionUnary, modulusWindowRoute, dyadicReadbackRoute,
      admissionCont, provenancePkg, admissionPkg⟩

end BEDC.Derived.RealCauchyModulusUp
