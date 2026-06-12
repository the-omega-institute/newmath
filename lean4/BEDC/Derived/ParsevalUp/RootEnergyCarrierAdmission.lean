import BEDC.Derived.ParsevalUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ParsevalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ParsevalCarrier [AskSetup] [PackageSetup]
    (fourier source pairing integral readback tolerance sealRow transport replay provenance
      name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: ParsevalUp BHist ProbeBundle Pkg PkgSig UnaryHistory Cont
  UnaryHistory fourier ∧ UnaryHistory source ∧ UnaryHistory pairing ∧
    UnaryHistory integral ∧ UnaryHistory readback ∧ UnaryHistory tolerance ∧
      UnaryHistory sealRow ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
        UnaryHistory provenance ∧ UnaryHistory name ∧ Cont fourier source pairing ∧
          Cont pairing integral readback ∧ Cont readback tolerance sealRow ∧
            Cont sealRow transport replay ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle name pkg

theorem ParsevalRootEnergyCarrierAdmission [AskSetup] [PackageSetup]
    {fourier source pairing integral readback tolerance sealRow transport replay provenance name
      rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ParsevalCarrier fourier source pairing integral readback tolerance sealRow transport replay
        provenance name bundle pkg →
      Cont sealRow replay rootRead →
        PkgSig bundle rootRead pkg →
          UnaryHistory fourier ∧ UnaryHistory source ∧ UnaryHistory pairing ∧
            UnaryHistory integral ∧ UnaryHistory readback ∧ UnaryHistory tolerance ∧
              UnaryHistory sealRow ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
                UnaryHistory rootRead ∧ Cont fourier source pairing ∧
                  Cont pairing integral readback ∧ Cont readback tolerance sealRow ∧
                    Cont sealRow transport replay ∧ Cont sealRow replay rootRead ∧
                      PkgSig bundle rootRead pkg := by
  -- BEDC touchpoint anchor: ParsevalCarrier BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier rootReplay rootPkg
  obtain ⟨fourierUnary, sourceUnary, pairingUnary, integralUnary, readbackUnary,
    toleranceUnary, sealUnary, transportUnary, replayUnary, _provenanceUnary, _nameUnary,
    fourierSourcePairing, pairingIntegralReadback, readbackToleranceSeal,
    sealTransportReplay, _provenancePkg, _namePkg⟩ := carrier
  have rootReadUnary : UnaryHistory rootRead :=
    unary_cont_closed sealUnary replayUnary rootReplay
  exact
    ⟨fourierUnary, sourceUnary, pairingUnary, integralUnary, readbackUnary, toleranceUnary,
      sealUnary, transportUnary, replayUnary, rootReadUnary, fourierSourcePairing,
      pairingIntegralReadback, readbackToleranceSeal, sealTransportReplay, rootReplay,
      rootPkg⟩

end BEDC.Derived.ParsevalUp
