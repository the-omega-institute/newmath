import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealApproximationEnvelopeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RealApproximationEnvelopePacket [AskSetup] [PackageSetup]
    (tolerance window dyadic classifier sealRow transports routes provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory
  UnaryHistory tolerance ∧ UnaryHistory window ∧ UnaryHistory dyadic ∧
    UnaryHistory classifier ∧ UnaryHistory sealRow ∧ UnaryHistory transports ∧
      UnaryHistory routes ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
        Cont tolerance window dyadic ∧ Cont dyadic classifier sealRow ∧
          Cont transports routes provenance ∧ PkgSig bundle provenance pkg ∧
            PkgSig bundle name pkg

theorem RealApproximationEnvelopeWindowReadbackTotality [AskSetup] [PackageSetup]
    {tolerance window dyadic classifier sealRow transports routes provenance name
      windowRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealApproximationEnvelopePacket tolerance window dyadic classifier sealRow transports
        routes provenance name bundle pkg →
      Cont tolerance window windowRead →
        PkgSig bundle windowRead pkg →
          UnaryHistory tolerance ∧ UnaryHistory window ∧ UnaryHistory windowRead ∧
            Cont tolerance window windowRead ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle windowRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro packet toleranceWindowRead windowReadPkg
  obtain ⟨toleranceUnary, windowUnary, _dyadicUnary, _classifierUnary, _sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, _toleranceWindowDyadic,
    _dyadicClassifierSeal, _transportsRoutesProvenance, provenancePkg, _namePkg⟩ :=
    packet
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed toleranceUnary windowUnary toleranceWindowRead
  exact
    ⟨toleranceUnary, windowUnary, windowReadUnary, toleranceWindowRead, provenancePkg,
      windowReadPkg⟩

end BEDC.Derived.RealApproximationEnvelopeUp
