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
    (vertices edges weights source target path incidence weightedPath endpoint before after
      predecessor relaxationStep relaxationLedger certificate : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  ShortestPathWeightedGraphCarrier vertices edges weights source target path incidence
      weightedPath endpoint bundle pkg ∧
    UnaryHistory before ∧ UnaryHistory after ∧ UnaryHistory predecessor ∧
      Cont before predecessor relaxationStep ∧ Cont endpoint relaxationStep relaxationLedger ∧
        Cont relaxationLedger after certificate ∧ PkgSig bundle certificate pkg

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

theorem ShortestPathRelaxationLedgerCarrier_continuation_closure [AskSetup] [PackageSetup]
    {vertices edges weights source target path incidence weightedPath endpoint before after
      predecessor relaxationStep relaxationLedger certificate : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ShortestPathWeightedGraphCarrier vertices edges weights source target path incidence
        weightedPath endpoint bundle pkg ->
      UnaryHistory before ->
        UnaryHistory after ->
          UnaryHistory predecessor ->
            Cont before predecessor relaxationStep ->
              Cont endpoint relaxationStep relaxationLedger ->
                Cont relaxationLedger after certificate ->
                  PkgSig bundle certificate pkg ->
                    ShortestPathRelaxationLedgerCarrier vertices edges weights source target
                        path incidence weightedPath endpoint before after predecessor
                        relaxationStep relaxationLedger certificate bundle pkg ∧
                      UnaryHistory relaxationStep ∧ UnaryHistory relaxationLedger ∧
                        UnaryHistory certificate ∧
                          hsame relaxationStep (append before predecessor) ∧
                            hsame relaxationLedger (append endpoint relaxationStep) ∧
                              hsame certificate (append relaxationLedger after) := by
  intro carrier beforeUnary afterUnary predecessorUnary relaxationStepRow relaxationLedgerRow
    certificateRow certificateSig
  have pathLedger := ShortestPathWeightedGraphCarrier_visible_path_ledger carrier
  have endpointUnary : UnaryHistory endpoint := pathLedger.right.right.left
  have relaxationStepUnary : UnaryHistory relaxationStep :=
    unary_cont_closed beforeUnary predecessorUnary relaxationStepRow
  have relaxationLedgerUnary : UnaryHistory relaxationLedger :=
    unary_cont_closed endpointUnary relaxationStepUnary relaxationLedgerRow
  have certificateUnary : UnaryHistory certificate :=
    unary_cont_closed relaxationLedgerUnary afterUnary certificateRow
  have relaxationCarrier :
      ShortestPathRelaxationLedgerCarrier vertices edges weights source target path incidence
        weightedPath endpoint before after predecessor relaxationStep relaxationLedger certificate
        bundle pkg :=
    ⟨carrier, beforeUnary, afterUnary, predecessorUnary, relaxationStepRow, relaxationLedgerRow,
      certificateRow, certificateSig⟩
  exact
    ⟨relaxationCarrier,
      relaxationStepUnary,
      relaxationLedgerUnary,
      certificateUnary,
      relaxationStepRow,
      relaxationLedgerRow,
      certificateRow⟩

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
