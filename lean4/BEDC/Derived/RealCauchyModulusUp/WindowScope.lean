import BEDC.Derived.RealCauchyModulusUp.TasteGate

namespace BEDC.Derived.RealCauchyModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealCauchyModulusCarrier_window_scope [AskSetup] [PackageSetup]
    {modulus windows dyadic readback sealRow transports routes provenance localCert precision
      scopedWindow scopedDyadic scopedSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCauchyModulusCarrier modulus windows dyadic readback sealRow transports routes provenance
        localCert bundle pkg →
      UnaryHistory precision →
        Cont windows precision scopedWindow →
          Cont scopedWindow dyadic scopedDyadic →
            Cont scopedDyadic readback scopedSeal →
              PkgSig bundle scopedSeal pkg →
                UnaryHistory modulus ∧ UnaryHistory windows ∧ UnaryHistory precision ∧
                  UnaryHistory scopedWindow ∧ UnaryHistory scopedDyadic ∧
                    UnaryHistory scopedSeal ∧ Cont modulus windows dyadic ∧
                      Cont windows precision scopedWindow ∧
                        Cont scopedWindow dyadic scopedDyadic ∧
                          Cont scopedDyadic readback scopedSeal ∧
                            PkgSig bundle provenance pkg ∧ PkgSig bundle scopedSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier precisionUnary windowPrecision dyadicScope sealScope scopedSealPkg
  obtain ⟨modulusUnary, windowsUnary, dyadicUnary, readbackUnary, _sealUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _localCertUnary, modulusWindowRoute,
      _dyadicReadbackRoute, _sealRoute, provenancePkg, _localSemantic⟩ := carrier
  have scopedWindowUnary : UnaryHistory scopedWindow :=
    unary_cont_closed windowsUnary precisionUnary windowPrecision
  have scopedDyadicUnary : UnaryHistory scopedDyadic :=
    unary_cont_closed scopedWindowUnary dyadicUnary dyadicScope
  have scopedSealUnary : UnaryHistory scopedSeal :=
    unary_cont_closed scopedDyadicUnary readbackUnary sealScope
  exact
    ⟨modulusUnary, windowsUnary, precisionUnary, scopedWindowUnary, scopedDyadicUnary,
      scopedSealUnary, modulusWindowRoute, windowPrecision, dyadicScope, sealScope,
      provenancePkg, scopedSealPkg⟩

end BEDC.Derived.RealCauchyModulusUp
