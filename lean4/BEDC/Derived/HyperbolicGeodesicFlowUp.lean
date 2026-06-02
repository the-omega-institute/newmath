import BEDC.Derived.HyperbolicGeodesicFlowUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.HyperbolicGeodesicFlowUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HyperbolicGeodesicFlowFixedEndNonescape [AskSetup] [PackageSetup]
    {geodesic endpoint boundary flow provenance name fixedRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory geodesic ->
      UnaryHistory endpoint ->
        UnaryHistory boundary ->
          UnaryHistory flow ->
            Cont geodesic endpoint fixedRead ->
              Cont fixedRead flow replayRead ->
                PkgSig bundle provenance pkg ->
                  PkgSig bundle name pkg ->
                    UnaryHistory fixedRead ∧ UnaryHistory replayRead ∧
                      Cont geodesic endpoint fixedRead ∧ Cont fixedRead flow replayRead ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory
  intro geodesicUnary endpointUnary _boundaryUnary flowUnary fixedRoute replayRoute
    provenancePkg namePkg
  have fixedUnary : UnaryHistory fixedRead :=
    unary_cont_closed geodesicUnary endpointUnary fixedRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed fixedUnary flowUnary replayRoute
  exact
    ⟨fixedUnary, replayUnary, fixedRoute, replayRoute, provenancePkg, namePkg⟩

end BEDC.Derived.HyperbolicGeodesicFlowUp
