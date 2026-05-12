import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BishopRealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BishopRealPacket [AskSetup] [PackageSetup]
    (schedule regular dyadic modulus located apartness realSeal transport routes provenance
      nameCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory schedule ∧ UnaryHistory regular ∧ UnaryHistory dyadic ∧
    UnaryHistory modulus ∧ UnaryHistory located ∧ UnaryHistory apartness ∧
      UnaryHistory realSeal ∧ UnaryHistory transport ∧ UnaryHistory routes ∧
        UnaryHistory provenance ∧ UnaryHistory nameCert ∧ Cont schedule regular dyadic ∧
          Cont dyadic modulus realSeal ∧ Cont transport routes provenance ∧
            PkgSig bundle provenance pkg

theorem BishopRealPacket_regseqrat_readback [AskSetup] [PackageSetup]
    {schedule regular dyadic modulus located apartness realSeal transport routes provenance
      nameCert readback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BishopRealPacket schedule regular dyadic modulus located apartness realSeal transport routes
        provenance nameCert bundle pkg ->
      Cont regular schedule readback ->
        PkgSig bundle readback pkg ->
          UnaryHistory schedule ∧ UnaryHistory regular ∧ UnaryHistory dyadic ∧
            UnaryHistory modulus ∧ UnaryHistory realSeal ∧ UnaryHistory readback ∧
              Cont regular schedule readback ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle readback pkg := by
  intro packet regularScheduleReadback readbackPkg
  rcases packet with
    ⟨scheduleUnary, regularUnary, dyadicUnary, modulusUnary, _locatedUnary,
      _apartnessUnary, realSealUnary, _transportUnary, _routesUnary, _provenanceUnary,
      _nameCertUnary, _scheduleRegularDyadic, _dyadicModulusSeal, _routeProvenance,
      provenancePkg⟩
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed regularUnary scheduleUnary regularScheduleReadback
  exact
    ⟨scheduleUnary, regularUnary, dyadicUnary, modulusUnary, realSealUnary, readbackUnary,
      regularScheduleReadback, provenancePkg, readbackPkg⟩

end BEDC.Derived.BishopRealUp
