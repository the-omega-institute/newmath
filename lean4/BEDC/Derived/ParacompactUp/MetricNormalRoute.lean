import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Derived.ParacompactUp.TasteGate

namespace BEDC.Derived.ParacompactUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ParacompactCarrier_metric_normal_route [AskSetup] [PackageSetup]
    {topology window cover refinement localFinite coverage normal urysohn metric transport replay
      provenance localName metricRead normalRead refinementExport : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory metric ->
      UnaryHistory transport ->
        UnaryHistory normal ->
          UnaryHistory urysohn ->
            UnaryHistory refinement ->
              Cont metric transport metricRead ->
                Cont normal urysohn normalRead ->
                  Cont metricRead normalRead refinementExport ->
                    PkgSig bundle provenance pkg ->
                      PkgSig bundle refinementExport pkg ->
                        UnaryHistory metricRead ∧ UnaryHistory normalRead ∧
                          UnaryHistory refinementExport ∧
                            Cont metric transport metricRead ∧
                              Cont normal urysohn normalRead ∧
                                Cont metricRead normalRead refinementExport ∧
                                  PkgSig bundle provenance pkg ∧
                                    PkgSig bundle refinementExport pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro metricUnary transportUnary normalUnary urysohnUnary _refinementUnary
    metricTransportRead normalUrysohnRead refinementRoute provenancePkg refinementPkg
  have metricReadUnary : UnaryHistory metricRead :=
    unary_cont_closed metricUnary transportUnary metricTransportRead
  have normalReadUnary : UnaryHistory normalRead :=
    unary_cont_closed normalUnary urysohnUnary normalUrysohnRead
  have refinementExportUnary : UnaryHistory refinementExport :=
    unary_cont_closed metricReadUnary normalReadUnary refinementRoute
  exact
    ⟨metricReadUnary, normalReadUnary, refinementExportUnary, metricTransportRead,
      normalUrysohnRead, refinementRoute, provenancePkg, refinementPkg⟩

end BEDC.Derived.ParacompactUp
