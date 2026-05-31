import BEDC.Derived.RealCauchyModulusUp.TasteGate

namespace BEDC.Derived.RealCauchyModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealCauchyModulusCarrier_uniform_cofinal_seal [AskSetup] [PackageSetup]
    {modulus windows dyadic readback sealRow transports routes provenance localCert precision
      refinedWindows refinedDyadic refinedSeal cofinalSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCauchyModulusCarrier modulus windows dyadic readback sealRow transports routes provenance
        localCert bundle pkg ->
      UnaryHistory precision ->
        Cont windows precision refinedWindows ->
          Cont refinedWindows dyadic refinedDyadic ->
            Cont refinedDyadic readback refinedSeal ->
              Cont refinedSeal sealRow cofinalSeal ->
                PkgSig bundle cofinalSeal pkg ->
                  UnaryHistory modulus ∧ UnaryHistory windows ∧ UnaryHistory dyadic ∧
                    UnaryHistory readback ∧ UnaryHistory sealRow ∧ UnaryHistory precision ∧
                      UnaryHistory refinedWindows ∧ UnaryHistory refinedDyadic ∧
                        UnaryHistory refinedSeal ∧ UnaryHistory cofinalSeal ∧
                          Cont modulus windows dyadic ∧
                            Cont windows precision refinedWindows ∧
                              Cont refinedWindows dyadic refinedDyadic ∧
                                Cont refinedDyadic readback refinedSeal ∧
                                  Cont refinedSeal sealRow cofinalSeal ∧
                                    PkgSig bundle provenance pkg ∧
                                      PkgSig bundle cofinalSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier precisionUnary windowsPrecision refinedDyadicCont refinedSealCont
  intro cofinalSealCont cofinalSealPkg
  obtain ⟨modulusUnary, windowsUnary, dyadicUnary, readbackUnary, sealUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _localCertUnary, modulusWindowRoute,
      _dyadicReadbackRoute, _sealRoute, provenancePkg, _localSemantic⟩ := carrier
  have refinedWindowsUnary : UnaryHistory refinedWindows :=
    unary_cont_closed windowsUnary precisionUnary windowsPrecision
  have refinedDyadicUnary : UnaryHistory refinedDyadic :=
    unary_cont_closed refinedWindowsUnary dyadicUnary refinedDyadicCont
  have refinedSealUnary : UnaryHistory refinedSeal :=
    unary_cont_closed refinedDyadicUnary readbackUnary refinedSealCont
  have cofinalSealUnary : UnaryHistory cofinalSeal :=
    unary_cont_closed refinedSealUnary sealUnary cofinalSealCont
  exact
    ⟨modulusUnary, windowsUnary, dyadicUnary, readbackUnary, sealUnary, precisionUnary,
      refinedWindowsUnary, refinedDyadicUnary, refinedSealUnary, cofinalSealUnary,
      modulusWindowRoute, windowsPrecision, refinedDyadicCont, refinedSealCont,
      cofinalSealCont, provenancePkg, cofinalSealPkg⟩

theorem RealCauchyModulusCarrier_uniform_cofinal_seal_certificate [AskSetup] [PackageSetup]
    {modulus windows dyadic readback sealRow transports routes provenance localCert precision
      refinedWindows refinedDyadic refinedSeal cofinalSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCauchyModulusCarrier modulus windows dyadic readback sealRow transports routes provenance
        localCert bundle pkg -> UnaryHistory precision ->
      Cont windows precision refinedWindows -> Cont refinedWindows dyadic refinedDyadic ->
        Cont refinedDyadic readback refinedSeal -> Cont refinedSeal sealRow cofinalSeal ->
          PkgSig bundle cofinalSeal pkg ->
            UnaryHistory cofinalSeal ∧ Cont refinedSeal sealRow cofinalSeal ∧
              PkgSig bundle cofinalSeal pkg ∧
                SemanticNameCert
                  (fun row : BHist => hsame row localCert ∧ UnaryHistory row)
                  (fun row : BHist => UnaryHistory row ∧ hsame row localCert)
                  (fun row : BHist => UnaryHistory row ∧ PkgSig bundle provenance pkg)
                  (fun row row' : BHist => hsame row row') := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont SemanticNameCert
  intro carrier precisionUnary windowsPrecision refinedDyadicCont refinedSealCont
  intro cofinalSealCont cofinalSealPkg
  obtain ⟨_modulusUnary, windowsUnary, dyadicUnary, readbackUnary, sealUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _localCertUnary, _modulusRoute,
      _dyadicRoute, _sealRoute, _provenancePkg, localSemantic⟩ := carrier
  have refinedWindowsUnary : UnaryHistory refinedWindows :=
    unary_cont_closed windowsUnary precisionUnary windowsPrecision
  have refinedDyadicUnary : UnaryHistory refinedDyadic :=
    unary_cont_closed refinedWindowsUnary dyadicUnary refinedDyadicCont
  have refinedSealUnary : UnaryHistory refinedSeal :=
    unary_cont_closed refinedDyadicUnary readbackUnary refinedSealCont
  have cofinalSealUnary : UnaryHistory cofinalSeal :=
    unary_cont_closed refinedSealUnary sealUnary cofinalSealCont
  exact ⟨cofinalSealUnary, cofinalSealCont, cofinalSealPkg, localSemantic⟩

end BEDC.Derived.RealCauchyModulusUp
