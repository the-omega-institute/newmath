import BEDC.Derived.ParsevalUp.RootEnergyCarrierAdmission

namespace BEDC.Derived.ParsevalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ParsevalFiniteFourierCarrierAdmission [AskSetup] [PackageSetup]
    {fourier source pairing integral readback tolerance sealRow transport replay provenance name
      coefficientRead energyRead equalityRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ParsevalCarrier fourier source pairing integral readback tolerance sealRow transport replay
        provenance name bundle pkg ->
      Cont fourier source coefficientRead ->
        Cont coefficientRead integral energyRead ->
          Cont energyRead sealRow equalityRead ->
            PkgSig bundle equalityRead pkg ->
              UnaryHistory fourier ∧ UnaryHistory source ∧ UnaryHistory pairing ∧
                UnaryHistory integral ∧ UnaryHistory readback ∧ UnaryHistory tolerance ∧
                  UnaryHistory sealRow ∧ UnaryHistory coefficientRead ∧
                    UnaryHistory energyRead ∧ UnaryHistory equalityRead ∧
                      Cont fourier source coefficientRead ∧
                        Cont coefficientRead integral energyRead ∧
                          Cont energyRead sealRow equalityRead ∧
                            PkgSig bundle provenance pkg ∧
                              PkgSig bundle equalityRead pkg := by
  -- BEDC touchpoint anchor: ParsevalCarrier BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier coefficientRoute energyRoute equalityRoute equalityPkg
  obtain ⟨fourierUnary, sourceUnary, pairingUnary, integralUnary, readbackUnary,
    toleranceUnary, sealRowUnary, _transportUnary, _replayUnary, _provenanceUnary,
      _nameUnary, _fourierSourcePairing, _pairingIntegralReadback,
        _readbackToleranceSeal, _sealTransportReplay, provenancePkg, _namePkg⟩ :=
    carrier
  have coefficientUnary : UnaryHistory coefficientRead :=
    unary_cont_closed fourierUnary sourceUnary coefficientRoute
  have energyUnary : UnaryHistory energyRead :=
    unary_cont_closed coefficientUnary integralUnary energyRoute
  have equalityUnary : UnaryHistory equalityRead :=
    unary_cont_closed energyUnary sealRowUnary equalityRoute
  exact
    ⟨fourierUnary, sourceUnary, pairingUnary, integralUnary, readbackUnary,
      toleranceUnary, sealRowUnary, coefficientUnary, energyUnary, equalityUnary,
      coefficientRoute, energyRoute, equalityRoute, provenancePkg, equalityPkg⟩

end BEDC.Derived.ParsevalUp
