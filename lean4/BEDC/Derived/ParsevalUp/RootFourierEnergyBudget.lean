import BEDC.Derived.ParsevalUp.RootFiniteCoefficientLedger

namespace BEDC.Derived.ParsevalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ParsevalRootFourierEnergyBudget [AskSetup] [PackageSetup]
    {fourier source pairing integral readback tolerance sealRow transport replay provenance name
      coefficientRead energyRead rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ParsevalCarrier fourier source pairing integral readback tolerance sealRow transport replay
        provenance name bundle pkg →
      Cont fourier source coefficientRead →
        Cont pairing integral energyRead →
          Cont sealRow replay rootRead →
            PkgSig bundle rootRead pkg →
              UnaryHistory fourier ∧ UnaryHistory source ∧ UnaryHistory pairing ∧
                UnaryHistory integral ∧ UnaryHistory coefficientRead ∧
                  UnaryHistory energyRead ∧ UnaryHistory rootRead ∧
                    Cont fourier source coefficientRead ∧
                      Cont pairing integral energyRead ∧ Cont readback tolerance sealRow ∧
                        Cont sealRow replay rootRead ∧ PkgSig bundle rootRead pkg := by
  -- BEDC touchpoint anchor: ParsevalCarrier BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier coefficientRoute energyRoute rootRoute rootPkg
  obtain ⟨fourierUnary, sourceUnary, pairingUnary, integralUnary, _readbackUnary,
    _toleranceUnary, sealUnary, _transportUnary, replayUnary, _provenanceUnary, _nameUnary,
    _fourierSourcePairing, _pairingIntegralReadback, readbackToleranceSeal,
    _sealTransportReplay, _provenancePkg, _namePkg⟩ := carrier
  have coefficientUnary : UnaryHistory coefficientRead :=
    unary_cont_closed fourierUnary sourceUnary coefficientRoute
  have energyUnary : UnaryHistory energyRead :=
    unary_cont_closed pairingUnary integralUnary energyRoute
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed sealUnary replayUnary rootRoute
  exact
    ⟨fourierUnary, sourceUnary, pairingUnary, integralUnary, coefficientUnary, energyUnary,
      rootUnary, coefficientRoute, energyRoute, readbackToleranceSeal, rootRoute, rootPkg⟩

end BEDC.Derived.ParsevalUp
