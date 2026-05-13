import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

/-!
# RealCompletenessUp finite carrier.
-/

namespace BEDC.Derived.RealCompletenessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RealCompletenessBHistCarrier [AskSetup] [PackageSetup]
    (family modulus selector dyadic windows readback «seal» transport route provenance cert
      endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory family ∧ UnaryHistory modulus ∧ UnaryHistory selector ∧ UnaryHistory dyadic ∧
    UnaryHistory windows ∧ UnaryHistory readback ∧ UnaryHistory «seal» ∧ UnaryHistory transport ∧
      UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory cert ∧ UnaryHistory endpoint ∧
        Cont transport route endpoint ∧ PkgSig bundle endpoint pkg

theorem RealCompletenessBHistCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {family modulus selector dyadic windows readback «seal» transport route provenance cert
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCompletenessBHistCarrier family modulus selector dyadic windows readback «seal» transport
        route provenance cert endpoint bundle pkg ->
      UnaryHistory family /\ UnaryHistory modulus /\ UnaryHistory selector /\
        UnaryHistory dyadic /\ UnaryHistory windows /\ UnaryHistory readback /\ UnaryHistory «seal» /\
          UnaryHistory transport /\ UnaryHistory route /\ UnaryHistory provenance /\
            UnaryHistory cert /\ UnaryHistory endpoint /\ Cont transport route endpoint /\
              PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier
  obtain ⟨familyUnary, modulusUnary, selectorUnary, dyadicUnary, windowsUnary, readbackUnary,
    sealUnary, transportUnary, routeUnary, provenanceUnary, certUnary, endpointUnary,
    endpointRoute, endpointPkg⟩ := carrier
  exact ⟨familyUnary, modulusUnary, selectorUnary, dyadicUnary, windowsUnary, readbackUnary,
    sealUnary, transportUnary, routeUnary, provenanceUnary, certUnary, endpointUnary,
    endpointRoute, endpointPkg⟩

theorem RealCompletenessBHistCarrier_diagonal_witness_schedule [AskSetup] [PackageSetup]
    {family modulus selector dyadic windows readback «seal» transport route provenance cert endpoint
      diagonal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCompletenessBHistCarrier family modulus selector dyadic windows readback «seal» transport
        route provenance cert endpoint bundle pkg →
      Cont selector dyadic diagonal →
        Cont diagonal windows readback →
          Cont readback «seal» endpoint →
            UnaryHistory selector ∧ UnaryHistory dyadic ∧ UnaryHistory diagonal ∧
              UnaryHistory windows ∧ UnaryHistory readback ∧ UnaryHistory «seal» ∧
                UnaryHistory endpoint ∧ Cont selector dyadic diagonal ∧
                  Cont diagonal windows readback ∧ Cont readback «seal» endpoint ∧
                    PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier selectorDyadic diagonalWindows readbackSeal
  obtain ⟨familyUnary, modulusUnary, selectorUnary, dyadicUnary, windowsUnary, readbackUnary,
    sealUnary, transportUnary, routeUnary, provenanceUnary, certUnary, endpointUnary,
    endpointRoute, endpointPkg⟩ := carrier
  have diagonalUnary : UnaryHistory diagonal :=
    unary_cont_closed selectorUnary dyadicUnary selectorDyadic
  have readbackUnary' : UnaryHistory readback :=
    unary_cont_closed diagonalUnary windowsUnary diagonalWindows
  have endpointUnary' : UnaryHistory endpoint :=
    unary_cont_closed readbackUnary' sealUnary readbackSeal
  exact
    ⟨selectorUnary, dyadicUnary, diagonalUnary, windowsUnary, readbackUnary', sealUnary,
      endpointUnary', selectorDyadic, diagonalWindows, readbackSeal, endpointPkg⟩

theorem RealCompletenessBHistCarrier_nonescape_boundary [AskSetup] [PackageSetup]
    {family modulus selector dyadic windows readback sealRow transport route provenance cert
      endpoint publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCompletenessBHistCarrier family modulus selector dyadic windows readback sealRow
        transport route provenance cert endpoint bundle pkg ->
      Cont sealRow cert publicRead ->
        UnaryHistory publicRead ∧ UnaryHistory sealRow ∧ UnaryHistory cert ∧
          UnaryHistory endpoint ∧ Cont transport route endpoint ∧ PkgSig bundle endpoint pkg := by
  intro carrier publicReadRow
  obtain ⟨_familyUnary, _modulusUnary, _selectorUnary, _dyadicUnary, _windowsUnary,
    _readbackUnary, sealUnary, _transportUnary, _routeUnary, _provenanceUnary, certUnary,
    endpointUnary, endpointRoute, endpointPkg⟩ := carrier
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed sealUnary certUnary publicReadRow
  exact ⟨publicReadUnary, sealUnary, certUnary, endpointUnary, endpointRoute, endpointPkg⟩

end BEDC.Derived.RealCompletenessUp
