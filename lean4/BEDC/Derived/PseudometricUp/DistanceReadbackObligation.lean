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

theorem PseudometricCarrier_distance_readback_obligation [AskSetup] [PackageSetup]
    {point distance dyadic stream readback sealRow zeroRow transport replay localName distanceRead
      zeroRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PseudometricCarrier point distance dyadic stream readback sealRow zeroRow transport replay localName
        bundle pkg →
      Cont stream readback distanceRead →
        Cont distanceRead zeroRow zeroRead →
          PkgSig bundle zeroRead pkg →
            UnaryHistory stream ∧ UnaryHistory readback ∧ UnaryHistory distanceRead ∧
              UnaryHistory zeroRead ∧ Cont stream readback distanceRead ∧
                Cont distanceRead zeroRow zeroRead ∧ PkgSig bundle localName pkg ∧
                  PkgSig bundle zeroRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier distanceRoute zeroRoute zeroPkg
  obtain ⟨_pointUnary, _distanceUnary, _dyadicUnary, streamUnary, readbackUnary,
    _sealUnary, zeroUnary, _transportUnary, _replayUnary, _localNameUnary,
    _streamReadbackDyadic, _dyadicSealZero, _localNameZero, localNamePkg⟩ := carrier
  have distanceReadUnary : UnaryHistory distanceRead :=
    unary_cont_closed streamUnary readbackUnary distanceRoute
  have zeroReadUnary : UnaryHistory zeroRead :=
    unary_cont_closed distanceReadUnary zeroUnary zeroRoute
  exact
    ⟨streamUnary, readbackUnary, distanceReadUnary, zeroReadUnary, distanceRoute, zeroRoute,
      localNamePkg, zeroPkg⟩

end BEDC.Derived.PseudometricUp
