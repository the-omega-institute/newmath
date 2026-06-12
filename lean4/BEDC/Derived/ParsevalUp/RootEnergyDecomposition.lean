import BEDC.Derived.ParsevalUp.RootEnergyCarrierAdmission

namespace BEDC.Derived.ParsevalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ParsevalRootEnergyDecomposition [AskSetup] [PackageSetup]
    {fourier source pairing integral readback tolerance sealRow transport replay provenance name
      coefficientRead energyRead sealRead rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ParsevalCarrier fourier source pairing integral readback tolerance sealRow transport replay
        provenance name bundle pkg →
      Cont fourier source coefficientRead →
        Cont pairing integral energyRead →
          Cont energyRead tolerance sealRead →
            Cont sealRead replay rootRead →
              PkgSig bundle rootRead pkg →
                UnaryHistory fourier ∧ UnaryHistory source ∧ UnaryHistory pairing ∧
                  UnaryHistory integral ∧ UnaryHistory readback ∧ UnaryHistory tolerance ∧
                    UnaryHistory sealRow ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
                      UnaryHistory coefficientRead ∧ UnaryHistory energyRead ∧
                        UnaryHistory sealRead ∧ UnaryHistory rootRead ∧
                          Cont fourier source coefficientRead ∧
                            Cont pairing integral energyRead ∧
                              Cont energyRead tolerance sealRead ∧
                                Cont sealRead replay rootRead ∧
                                  PkgSig bundle provenance pkg ∧
                                    PkgSig bundle rootRead pkg := by
  -- BEDC touchpoint anchor: ParsevalCarrier BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier coefficientRoute energyRoute sealRoute rootRoute rootPkg
  obtain ⟨fourierUnary, sourceUnary, pairingUnary, integralUnary, readbackUnary,
    toleranceUnary, sealUnary, transportUnary, replayUnary, _provenanceUnary, _nameUnary,
    _fourierSourcePairing, _pairingIntegralReadback, _readbackToleranceSeal,
    _sealTransportReplay, provenancePkg, _namePkg⟩ := carrier
  have coefficientUnary : UnaryHistory coefficientRead :=
    unary_cont_closed fourierUnary sourceUnary coefficientRoute
  have energyUnary : UnaryHistory energyRead :=
    unary_cont_closed pairingUnary integralUnary energyRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed energyUnary toleranceUnary sealRoute
  have rootReadUnary : UnaryHistory rootRead :=
    unary_cont_closed sealReadUnary replayUnary rootRoute
  exact
    ⟨fourierUnary, sourceUnary, pairingUnary, integralUnary, readbackUnary, toleranceUnary,
      sealUnary, transportUnary, replayUnary, coefficientUnary, energyUnary, sealReadUnary,
      rootReadUnary, coefficientRoute, energyRoute, sealRoute, rootRoute, provenancePkg,
      rootPkg⟩

end BEDC.Derived.ParsevalUp
