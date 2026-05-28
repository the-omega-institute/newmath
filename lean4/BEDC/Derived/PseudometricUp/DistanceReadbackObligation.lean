import BEDC.Derived.PseudometricUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.PseudometricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def PseudometricCarrier [AskSetup] [PackageSetup]
    (point distance dyadic stream readback realSeal zero transport replay cert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory point ∧ UnaryHistory distance ∧ UnaryHistory dyadic ∧ UnaryHistory stream ∧
    UnaryHistory readback ∧ UnaryHistory realSeal ∧ UnaryHistory zero ∧
      UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory cert ∧
        Cont point distance dyadic ∧ Cont stream readback realSeal ∧
          Cont transport replay cert ∧ PkgSig bundle cert pkg

theorem PseudometricCarrier_distance_readback_obligation [AskSetup] [PackageSetup]
    {point distance dyadic stream readback realSeal zero transport replay cert distanceRead
      zeroRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PseudometricCarrier point distance dyadic stream readback realSeal zero transport replay cert
        bundle pkg →
      Cont stream readback distanceRead →
        Cont distanceRead zero zeroRead →
          PkgSig bundle zeroRead pkg →
            UnaryHistory stream ∧ UnaryHistory readback ∧ UnaryHistory distanceRead ∧
              UnaryHistory zeroRead ∧ Cont stream readback distanceRead ∧
                Cont distanceRead zero zeroRead ∧ PkgSig bundle cert pkg ∧
                  PkgSig bundle zeroRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier distanceRoute zeroRoute zeroPkg
  obtain ⟨_pointUnary, _distanceUnary, _dyadicUnary, streamUnary, readbackUnary,
    _realSealUnary, zeroUnary, _transportUnary, _replayUnary, _certUnary, _pointDistance,
    _streamReadback, _transportReplay, certPkg⟩ := carrier
  have distanceReadUnary : UnaryHistory distanceRead :=
    unary_cont_closed streamUnary readbackUnary distanceRoute
  have zeroReadUnary : UnaryHistory zeroRead :=
    unary_cont_closed distanceReadUnary zeroUnary zeroRoute
  exact
    ⟨streamUnary, readbackUnary, distanceReadUnary, zeroReadUnary, distanceRoute, zeroRoute,
      certPkg, zeroPkg⟩

end BEDC.Derived.PseudometricUp
