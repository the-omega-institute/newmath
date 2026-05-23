import BEDC.Derived.RealCauchyModulusUp.TasteGate

namespace BEDC.Derived.RealCauchyModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealCauchyModulusCarrier_root_unblock_scope [AskSetup] [PackageSetup]
    {modulus windows dyadic readback sealRow transports routes provenance localCert
      unblockRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCauchyModulusCarrier modulus windows dyadic readback sealRow transports routes provenance
        localCert bundle pkg →
      Cont provenance localCert unblockRead →
        PkgSig bundle unblockRead pkg →
          UnaryHistory modulus ∧ UnaryHistory windows ∧ UnaryHistory dyadic ∧
            UnaryHistory readback ∧ UnaryHistory sealRow ∧ UnaryHistory provenance ∧
              UnaryHistory localCert ∧ UnaryHistory unblockRead ∧
                Cont modulus windows dyadic ∧ Cont dyadic readback sealRow ∧
                  Cont sealRow routes provenance ∧ Cont provenance localCert unblockRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle unblockRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier unblockCont unblockPkg
  obtain ⟨modulusUnary, windowsUnary, dyadicUnary, readbackUnary, sealUnary,
    _transportsUnary, _routesUnary, provenanceUnary, localCertUnary, modulusWindowRoute,
      dyadicReadbackRoute, sealRoute, provenancePkg, _localSemantic⟩ := carrier
  have unblockUnary : UnaryHistory unblockRead :=
    unary_cont_closed provenanceUnary localCertUnary unblockCont
  exact
    ⟨modulusUnary, windowsUnary, dyadicUnary, readbackUnary, sealUnary, provenanceUnary,
      localCertUnary, unblockUnary, modulusWindowRoute, dyadicReadbackRoute, sealRoute,
      unblockCont, provenancePkg, unblockPkg⟩

end BEDC.Derived.RealCauchyModulusUp
