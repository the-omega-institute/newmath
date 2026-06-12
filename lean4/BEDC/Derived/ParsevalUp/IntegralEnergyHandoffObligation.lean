import BEDC.Derived.ParsevalUp.RootEnergyCarrierAdmission

namespace BEDC.Derived.ParsevalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ParsevalIntegralEnergyHandoffObligation [AskSetup] [PackageSetup]
    {fourier source pairing integral readback tolerance sealRow transport replay provenance name
      coefficientRead energyRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ParsevalCarrier fourier source pairing integral readback tolerance sealRow transport replay
        provenance name bundle pkg →
      Cont fourier source coefficientRead →
        Cont pairing integral energyRead →
          Cont energyRead sealRow sealRead →
            PkgSig bundle sealRead pkg →
              UnaryHistory fourier ∧ UnaryHistory source ∧ UnaryHistory pairing ∧
                UnaryHistory integral ∧ UnaryHistory coefficientRead ∧
                  UnaryHistory energyRead ∧ UnaryHistory sealRead ∧
                    Cont fourier source coefficientRead ∧
                      Cont pairing integral energyRead ∧ Cont energyRead sealRow sealRead ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: ParsevalCarrier BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier coefficientRoute energyRoute sealRoute sealPkg
  obtain ⟨fourierUnary, sourceUnary, pairingUnary, integralUnary, _readbackUnary,
    _toleranceUnary, sealUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _nameUnary, _fourierSourcePairing, _pairingIntegralReadback,
    _readbackToleranceSeal, _sealTransportReplay, provenancePkg, _namePkg⟩ := carrier
  have coefficientUnary : UnaryHistory coefficientRead :=
    unary_cont_closed fourierUnary sourceUnary coefficientRoute
  have energyUnary : UnaryHistory energyRead :=
    unary_cont_closed pairingUnary integralUnary energyRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed energyUnary sealUnary sealRoute
  exact
    ⟨fourierUnary, sourceUnary, pairingUnary, integralUnary, coefficientUnary, energyUnary,
      sealReadUnary, coefficientRoute, energyRoute, sealRoute, provenancePkg, sealPkg⟩

end BEDC.Derived.ParsevalUp
