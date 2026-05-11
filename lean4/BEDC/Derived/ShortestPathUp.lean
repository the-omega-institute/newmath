import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ShortestPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ShortestPathWeightedGraphCarrier [AskSetup] [PackageSetup]
    (vertices edges weights source target path incidence weightedPath endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory vertices ∧ UnaryHistory edges ∧ UnaryHistory weights ∧
    UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory path ∧
      Cont vertices edges incidence ∧ Cont incidence weights weightedPath ∧
        Cont weightedPath path endpoint ∧ PkgSig bundle endpoint pkg

def ShortestPathRelaxationLedgerCarrier [AskSetup] [PackageSetup]
    (vertices edges weights source target path incidence weightedPath endpoint beforeAfter
      predecessor relaxation transport : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  ShortestPathWeightedGraphCarrier vertices edges weights source target path incidence
      weightedPath endpoint bundle pkg ∧
    UnaryHistory beforeAfter ∧ UnaryHistory relaxation ∧
      Cont endpoint beforeAfter predecessor ∧
        Cont predecessor relaxation transport ∧ PkgSig bundle transport pkg

theorem ShortestPathWeightedGraphCarrier_source_rows [AskSetup] [PackageSetup]
    {vertices edges weights source target path incidence weightedPath endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ShortestPathWeightedGraphCarrier vertices edges weights source target path incidence
        weightedPath endpoint bundle pkg ->
      UnaryHistory vertices ∧ UnaryHistory edges ∧ UnaryHistory weights ∧
        UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory path ∧
          Cont vertices edges incidence ∧ Cont incidence weights weightedPath ∧
            Cont weightedPath path endpoint ∧ PkgSig bundle endpoint pkg := by
  intro carrier
  cases carrier with
  | intro verticesUnary rest =>
      cases rest with
      | intro edgesUnary rest =>
          cases rest with
          | intro weightsUnary rest =>
              cases rest with
              | intro sourceUnary rest =>
                  cases rest with
                  | intro targetUnary rest =>
                      cases rest with
                      | intro pathUnary rest =>
                          cases rest with
                          | intro incidenceRow rest =>
                              cases rest with
                              | intro weightedPathRow rest =>
                                  cases rest with
                                  | intro endpointRow pkgRow =>
                                      exact
                                        ⟨verticesUnary,
                                          edgesUnary,
                                          weightsUnary,
                                          sourceUnary,
                                          targetUnary,
                                          pathUnary,
                                          incidenceRow,
                                          weightedPathRow,
                                          endpointRow,
                                          pkgRow⟩

theorem ShortestPathWeightedGraphCarrier_visible_path_ledger [AskSetup] [PackageSetup]
    {vertices edges weights source target path incidence weightedPath endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ShortestPathWeightedGraphCarrier vertices edges weights source target path incidence
        weightedPath endpoint bundle pkg ->
      UnaryHistory incidence ∧ UnaryHistory weightedPath ∧ UnaryHistory endpoint ∧
        hsame incidence (append vertices edges) ∧ hsame weightedPath (append incidence weights) ∧
          hsame endpoint (append weightedPath path) ∧ PkgSig bundle endpoint pkg := by
  intro carrier
  have incidenceUnary : UnaryHistory incidence :=
    unary_cont_closed carrier.left carrier.right.left
      carrier.right.right.right.right.right.right.left
  have weightedPathUnary : UnaryHistory weightedPath :=
    unary_cont_closed incidenceUnary carrier.right.right.left
      carrier.right.right.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed weightedPathUnary carrier.right.right.right.right.right.left
      carrier.right.right.right.right.right.right.right.right.left
  exact
    ⟨incidenceUnary, weightedPathUnary, endpointUnary,
      carrier.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right.right⟩

theorem ShortestPathWeightedGraphCarrier_endpoint_expanded_boundary [AskSetup] [PackageSetup]
    {vertices edges weights source target path incidence weightedPath endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ShortestPathWeightedGraphCarrier vertices edges weights source target path incidence
        weightedPath endpoint bundle pkg ->
      hsame endpoint (append (append (append vertices edges) weights) path) ∧
        PkgSig bundle endpoint pkg := by
  intro carrier
  have incidenceCont : Cont vertices edges incidence :=
    carrier.right.right.right.right.right.right.left
  have weightedPathCont : Cont incidence weights weightedPath :=
    carrier.right.right.right.right.right.right.right.left
  have endpointCont : Cont weightedPath path endpoint :=
    carrier.right.right.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle endpoint pkg :=
    carrier.right.right.right.right.right.right.right.right.right
  cases incidenceCont
  cases weightedPathCont
  cases endpointCont
  exact And.intro rfl pkgSig

theorem ShortestPathWeightedGraphCarrier_relaxation_cont_closure [AskSetup] [PackageSetup]
    {vertices edges weights source target path incidence weightedPath endpoint beforeAfter
      predecessor relaxation transport : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ShortestPathWeightedGraphCarrier vertices edges weights source target path incidence
        weightedPath endpoint bundle pkg ->
      Cont endpoint beforeAfter predecessor ->
        Cont predecessor relaxation transport ->
          PkgSig bundle transport pkg ->
            UnaryHistory beforeAfter ->
              UnaryHistory relaxation ->
                ShortestPathRelaxationLedgerCarrier vertices edges weights source target path
                    incidence weightedPath endpoint beforeAfter predecessor relaxation transport
                    bundle pkg ∧
                  UnaryHistory predecessor ∧ UnaryHistory transport ∧
                    hsame predecessor (append endpoint beforeAfter) ∧
                      hsame transport (append predecessor relaxation) := by
  intro carrier predecessorRow transportRow transportPkg beforeAfterUnary relaxationUnary
  have incidenceUnary : UnaryHistory incidence :=
    unary_cont_closed carrier.left carrier.right.left
      carrier.right.right.right.right.right.right.left
  have weightedPathUnary : UnaryHistory weightedPath :=
    unary_cont_closed incidenceUnary carrier.right.right.left
      carrier.right.right.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed weightedPathUnary carrier.right.right.right.right.right.left
      carrier.right.right.right.right.right.right.right.right.left
  have predecessorUnary : UnaryHistory predecessor :=
    unary_cont_closed endpointUnary beforeAfterUnary predecessorRow
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed predecessorUnary relaxationUnary transportRow
  exact
    ⟨⟨carrier, beforeAfterUnary, relaxationUnary, predecessorRow, transportRow, transportPkg⟩,
      predecessorUnary,
      transportUnary,
      predecessorRow,
      transportRow⟩

theorem ShortestPathWeightedGraphCarrier_visible_relaxation_namecert_surface [AskSetup]
    [PackageSetup]
    {vertices edges weights source target path incidence weightedPath endpoint beforeAfter
      predecessor relaxation transport : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ShortestPathRelaxationLedgerCarrier vertices edges weights source target path incidence
        weightedPath endpoint beforeAfter predecessor relaxation transport bundle pkg ->
      UnaryHistory incidence ∧ UnaryHistory weightedPath ∧ UnaryHistory endpoint ∧
        UnaryHistory predecessor ∧ UnaryHistory transport ∧
          Cont vertices edges incidence ∧ Cont incidence weights weightedPath ∧
            Cont weightedPath path endpoint ∧ Cont endpoint beforeAfter predecessor ∧
              Cont predecessor relaxation transport ∧ PkgSig bundle endpoint pkg ∧
                PkgSig bundle transport pkg := by
  intro ledger
  have carrier : ShortestPathWeightedGraphCarrier vertices edges weights source target path
      incidence weightedPath endpoint bundle pkg := ledger.left
  have incidenceUnary : UnaryHistory incidence :=
    unary_cont_closed carrier.left carrier.right.left
      carrier.right.right.right.right.right.right.left
  have weightedPathUnary : UnaryHistory weightedPath :=
    unary_cont_closed incidenceUnary carrier.right.right.left
      carrier.right.right.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed weightedPathUnary carrier.right.right.right.right.right.left
      carrier.right.right.right.right.right.right.right.right.left
  have beforeAfterUnary : UnaryHistory beforeAfter := ledger.right.left
  have relaxationUnary : UnaryHistory relaxation := ledger.right.right.left
  have predecessorUnary : UnaryHistory predecessor :=
    unary_cont_closed endpointUnary beforeAfterUnary ledger.right.right.right.left
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed predecessorUnary relaxationUnary ledger.right.right.right.right.left
  exact
    ⟨incidenceUnary,
      weightedPathUnary,
      endpointUnary,
      predecessorUnary,
      transportUnary,
      carrier.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right.left,
      ledger.right.right.right.left,
      ledger.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right.right,
      ledger.right.right.right.right.right⟩

theorem ShortestPathWeightedGraphCarrier_relaxation_certificate_scope [AskSetup] [PackageSetup]
    {vertices edges weights source target path incidence weightedPath endpoint relaxation
      certificate : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ShortestPathWeightedGraphCarrier vertices edges weights source target path incidence
        weightedPath endpoint bundle pkg ->
      Cont source target relaxation ->
        Cont endpoint relaxation certificate ->
          UnaryHistory incidence ∧ UnaryHistory weightedPath ∧ UnaryHistory endpoint ∧
            UnaryHistory relaxation ∧ UnaryHistory certificate ∧
              hsame incidence (append vertices edges) ∧
                hsame weightedPath (append incidence weights) ∧
                  hsame endpoint (append weightedPath path) ∧
                    hsame relaxation (append source target) ∧
                      hsame certificate (append endpoint relaxation) ∧
                        PkgSig bundle endpoint pkg := by
  intro carrier relaxationRow certificateRow
  have verticesUnary : UnaryHistory vertices := carrier.left
  have edgesUnary : UnaryHistory edges := carrier.right.left
  have weightsUnary : UnaryHistory weights := carrier.right.right.left
  have sourceUnary : UnaryHistory source := carrier.right.right.right.left
  have targetUnary : UnaryHistory target := carrier.right.right.right.right.left
  have pathUnary : UnaryHistory path := carrier.right.right.right.right.right.left
  have incidenceRow : Cont vertices edges incidence :=
    carrier.right.right.right.right.right.right.left
  have weightedPathRow : Cont incidence weights weightedPath :=
    carrier.right.right.right.right.right.right.right.left
  have endpointRow : Cont weightedPath path endpoint :=
    carrier.right.right.right.right.right.right.right.right.left
  have incidenceUnary : UnaryHistory incidence :=
    unary_cont_closed verticesUnary edgesUnary incidenceRow
  have weightedPathUnary : UnaryHistory weightedPath :=
    unary_cont_closed incidenceUnary weightsUnary weightedPathRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed weightedPathUnary pathUnary endpointRow
  have relaxationUnary : UnaryHistory relaxation :=
    unary_cont_closed sourceUnary targetUnary relaxationRow
  have certificateUnary : UnaryHistory certificate :=
    unary_cont_closed endpointUnary relaxationUnary certificateRow
  exact
    ⟨incidenceUnary,
      weightedPathUnary,
      endpointUnary,
      relaxationUnary,
      certificateUnary,
      incidenceRow,
      weightedPathRow,
      endpointRow,
      relaxationRow,
      certificateRow,
      carrier.right.right.right.right.right.right.right.right.right⟩

theorem ShortestPathWeightedGraphCarrier_relaxation_soundness [AskSetup] [PackageSetup]
    {vertices edges weights source target path incidence weightedPath endpoint relaxation
      certificate predecessor soundness : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ShortestPathWeightedGraphCarrier vertices edges weights source target path incidence
        weightedPath endpoint bundle pkg ->
      Cont source target relaxation ->
        Cont endpoint relaxation certificate ->
          Cont relaxation path predecessor ->
            Cont predecessor endpoint soundness ->
              UnaryHistory relaxation ∧ UnaryHistory certificate ∧
                UnaryHistory predecessor ∧ UnaryHistory soundness ∧
                  hsame relaxation (append source target) ∧
                    hsame certificate (append endpoint relaxation) ∧
                      hsame predecessor (append relaxation path) ∧
                        hsame soundness (append predecessor endpoint) ∧
                          PkgSig bundle endpoint pkg := by
  intro carrier relaxationRow certificateRow predecessorRow soundnessRow
  have sourceUnary : UnaryHistory source := carrier.right.right.right.left
  have targetUnary : UnaryHistory target := carrier.right.right.right.right.left
  have pathUnary : UnaryHistory path := carrier.right.right.right.right.right.left
  have incidenceUnary : UnaryHistory incidence :=
    unary_cont_closed carrier.left carrier.right.left
      carrier.right.right.right.right.right.right.left
  have weightedPathUnary : UnaryHistory weightedPath :=
    unary_cont_closed incidenceUnary carrier.right.right.left
      carrier.right.right.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed weightedPathUnary pathUnary
      carrier.right.right.right.right.right.right.right.right.left
  have relaxationUnary : UnaryHistory relaxation :=
    unary_cont_closed sourceUnary targetUnary relaxationRow
  have certificateUnary : UnaryHistory certificate :=
    unary_cont_closed endpointUnary relaxationUnary certificateRow
  have predecessorUnary : UnaryHistory predecessor :=
    unary_cont_closed relaxationUnary pathUnary predecessorRow
  have soundnessUnary : UnaryHistory soundness :=
    unary_cont_closed predecessorUnary endpointUnary soundnessRow
  exact
    ⟨relaxationUnary,
      certificateUnary,
      predecessorUnary,
      soundnessUnary,
      relaxationRow,
      certificateRow,
      predecessorRow,
      soundnessRow,
      carrier.right.right.right.right.right.right.right.right.right⟩

theorem ShortestPathWeightedGraphCarrier_finite_edge_exhaustion [AskSetup] [PackageSetup]
    {vertices edges weights source target path incidence weightedPath endpoint stepLedger
      edgeEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ShortestPathWeightedGraphCarrier vertices edges weights source target path incidence
        weightedPath endpoint bundle pkg ->
      Cont source target stepLedger ->
        Cont stepLedger incidence edgeEndpoint ->
          UnaryHistory stepLedger ∧ UnaryHistory edgeEndpoint ∧
            hsame stepLedger (append source target) ∧
              hsame edgeEndpoint (append stepLedger incidence) ∧
                PkgSig bundle endpoint pkg := by
  intro carrier stepLedgerRow edgeEndpointRow
  have sourceUnary : UnaryHistory source := carrier.right.right.right.left
  have targetUnary : UnaryHistory target := carrier.right.right.right.right.left
  have incidenceUnary : UnaryHistory incidence :=
    unary_cont_closed carrier.left carrier.right.left
      carrier.right.right.right.right.right.right.left
  have stepLedgerUnary : UnaryHistory stepLedger :=
    unary_cont_closed sourceUnary targetUnary stepLedgerRow
  have edgeEndpointUnary : UnaryHistory edgeEndpoint :=
    unary_cont_closed stepLedgerUnary incidenceUnary edgeEndpointRow
  exact
    ⟨stepLedgerUnary,
      edgeEndpointUnary,
      stepLedgerRow,
      edgeEndpointRow,
      carrier.right.right.right.right.right.right.right.right.right⟩

theorem ShortestPathWeightedGraphCarrier_weight_readback [AskSetup] [PackageSetup]
    {vertices edges weights source target path incidence weightedPath endpoint totalWeight
      weightLedger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ShortestPathWeightedGraphCarrier vertices edges weights source target path incidence
        weightedPath endpoint bundle pkg ->
      Cont weights path totalWeight ->
        Cont endpoint totalWeight weightLedger ->
          UnaryHistory totalWeight ∧ UnaryHistory weightLedger ∧
            hsame totalWeight (append weights path) ∧
              hsame weightLedger (append endpoint totalWeight) ∧
                PkgSig bundle endpoint pkg := by
  intro carrier totalWeightRow weightLedgerRow
  have weightsUnary : UnaryHistory weights := carrier.right.right.left
  have pathUnary : UnaryHistory path := carrier.right.right.right.right.right.left
  have incidenceUnary : UnaryHistory incidence :=
    unary_cont_closed carrier.left carrier.right.left
      carrier.right.right.right.right.right.right.left
  have weightedPathUnary : UnaryHistory weightedPath :=
    unary_cont_closed incidenceUnary weightsUnary
      carrier.right.right.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed weightedPathUnary pathUnary
      carrier.right.right.right.right.right.right.right.right.left
  have totalWeightUnary : UnaryHistory totalWeight :=
    unary_cont_closed weightsUnary pathUnary totalWeightRow
  have weightLedgerUnary : UnaryHistory weightLedger :=
    unary_cont_closed endpointUnary totalWeightUnary weightLedgerRow
  exact
    ⟨totalWeightUnary,
      weightLedgerUnary,
      totalWeightRow,
      weightLedgerRow,
      carrier.right.right.right.right.right.right.right.right.right⟩

theorem ShortestPathVisiblePathLedger [AskSetup] [PackageSetup]
    {vertices edges weights source target incidence path weightLedger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory vertices -> UnaryHistory edges -> UnaryHistory weights -> UnaryHistory source ->
      UnaryHistory target -> Cont vertices edges incidence -> Cont incidence weights path ->
        Cont source target weightLedger -> Cont path weightLedger endpoint ->
          PkgSig bundle endpoint pkg ->
            UnaryHistory incidence ∧ UnaryHistory path ∧ UnaryHistory weightLedger ∧
              UnaryHistory endpoint ∧ hsame incidence (append vertices edges) ∧
                hsame path (append incidence weights) ∧
                  hsame weightLedger (append source target) ∧
                    hsame endpoint (append path weightLedger) ∧ PkgSig bundle endpoint pkg := by
  intro verticesUnary edgesUnary weightsUnary sourceUnary targetUnary incidenceRow pathRow
    weightLedgerRow endpointRow pkgSig
  have incidenceUnary : UnaryHistory incidence :=
    unary_cont_closed verticesUnary edgesUnary incidenceRow
  have pathUnary : UnaryHistory path :=
    unary_cont_closed incidenceUnary weightsUnary pathRow
  have weightLedgerUnary : UnaryHistory weightLedger :=
    unary_cont_closed sourceUnary targetUnary weightLedgerRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed pathUnary weightLedgerUnary endpointRow
  exact
    ⟨incidenceUnary, pathUnary, weightLedgerUnary, endpointUnary, incidenceRow, pathRow,
      weightLedgerRow, endpointRow, pkgSig⟩

theorem ShortestPathRelaxationCertificate_scope [AskSetup] [PackageSetup]
    {vertices edges weights source target incidence path weightLedger endpoint relaxation
      relaxationEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory vertices ->
      UnaryHistory edges ->
        UnaryHistory weights ->
          UnaryHistory source ->
            UnaryHistory target ->
              Cont vertices edges incidence ->
                Cont incidence weights path ->
                  Cont source target weightLedger ->
                    Cont path weightLedger endpoint ->
                      Cont path endpoint relaxation ->
                        Cont relaxation weights relaxationEndpoint ->
                          PkgSig bundle relaxationEndpoint pkg ->
                            UnaryHistory incidence ∧ UnaryHistory path ∧
                              UnaryHistory weightLedger ∧ UnaryHistory endpoint ∧
                                UnaryHistory relaxation ∧ UnaryHistory relaxationEndpoint ∧
                                  hsame incidence (append vertices edges) ∧
                                    hsame path (append incidence weights) ∧
                                      hsame weightLedger (append source target) ∧
                                        hsame endpoint (append path weightLedger) ∧
                                          hsame relaxation (append path endpoint) ∧
                                            hsame relaxationEndpoint
                                              (append relaxation weights) ∧
                                              PkgSig bundle relaxationEndpoint pkg := by
  intro verticesUnary edgesUnary weightsUnary sourceUnary targetUnary incidenceRow pathRow
    weightLedgerRow endpointRow relaxationRow relaxationEndpointRow pkgSig
  have incidenceUnary : UnaryHistory incidence :=
    unary_cont_closed verticesUnary edgesUnary incidenceRow
  have pathUnary : UnaryHistory path :=
    unary_cont_closed incidenceUnary weightsUnary pathRow
  have weightLedgerUnary : UnaryHistory weightLedger :=
    unary_cont_closed sourceUnary targetUnary weightLedgerRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed pathUnary weightLedgerUnary endpointRow
  have relaxationUnary : UnaryHistory relaxation :=
    unary_cont_closed pathUnary endpointUnary relaxationRow
  have relaxationEndpointUnary : UnaryHistory relaxationEndpoint :=
    unary_cont_closed relaxationUnary weightsUnary relaxationEndpointRow
  exact
    ⟨incidenceUnary,
      pathUnary,
      weightLedgerUnary,
      endpointUnary,
      relaxationUnary,
      relaxationEndpointUnary,
      incidenceRow,
      pathRow,
      weightLedgerRow,
      endpointRow,
      relaxationRow,
      relaxationEndpointRow,
      pkgSig⟩

end BEDC.Derived.ShortestPathUp
