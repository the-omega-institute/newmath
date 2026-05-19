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

def RealApproximationEnvelopeCarrier [AskSetup] [PackageSetup]
    (tolerance window dyadic classifier sealRow transport route provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory
  UnaryHistory tolerance ∧ UnaryHistory window ∧ UnaryHistory dyadic ∧
    UnaryHistory classifier ∧ UnaryHistory sealRow ∧ UnaryHistory transport ∧
      UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
        Cont tolerance window route ∧ Cont window dyadic classifier ∧
          Cont classifier sealRow transport ∧ PkgSig bundle provenance pkg ∧
            PkgSig bundle name pkg

theorem RealApproximationEnvelope_window_readback_totality [AskSetup] [PackageSetup]
    {tolerance window dyadic classifier sealRow transport route provenance name windowRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealApproximationEnvelopeCarrier tolerance window dyadic classifier sealRow transport
        route provenance name bundle pkg →
      Cont tolerance window windowRead →
        PkgSig bundle windowRead pkg →
          UnaryHistory tolerance ∧ UnaryHistory window ∧ UnaryHistory windowRead ∧
            Cont tolerance window windowRead ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle name pkg ∧ PkgSig bundle windowRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier toleranceWindowRead windowReadPkg
  obtain ⟨toleranceUnary, windowUnary, _dyadicUnary, _classifierUnary, _sealUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _nameUnary, _toleranceWindowRoute,
    _windowDyadicClassifier, _classifierSealTransport, provenancePkg, namePkg⟩ :=
    carrier
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed toleranceUnary windowUnary toleranceWindowRead
  exact
    ⟨toleranceUnary, windowUnary, windowReadUnary, toleranceWindowRead, provenancePkg,
      namePkg, windowReadPkg⟩

end BEDC.Derived.RealApproximationEnvelopeUp
