import BEDC.Derived.RHRoute.EndpointBisectionCertificate
import BEDC.Derived.RHRoute.RecursiveParityTower
import BEDC.Derived.RHRoute.RouteClosureSeparation

namespace BEDC.Derived.RHRoute.ParityClosureTowerCertificate

open BEDC.Derived.RHRoute.EndpointBisectionCertificate
open BEDC.Derived.RHRoute.RecursiveParityTower
open BEDC.Derived.RHRoute.RecursiveSpectralZeroHierarchy
open BEDC.Derived.RHRoute.RecursiveTower
open BEDC.Derived.RHRoute.RouteClosureSeparation
open BEDC.Derived.RHRoute.ZeroGenerationInitiality

abbrev TowerParity :=
  BEDC.Derived.RHRoute.RecursiveParityTower.TowerParity

abbrev natParity :=
  BEDC.Derived.RHRoute.RecursiveParityTower.natParity

abbrev RecursiveParityTower :=
  BEDC.Derived.RHRoute.RecursiveParityTower.RecursiveParityTower

abbrev EndpointDyadicInterval :=
  BEDC.Derived.RHRoute.EndpointBisectionCertificate.EndpointDyadicInterval

abbrev EndpointDyadicDiameterContract :=
  BEDC.Derived.RHRoute.EndpointBisectionCertificate.EndpointDyadicDiameterContract

abbrev EndpointBranch :=
  BEDC.Derived.RHRoute.EndpointBisectionCertificate.EndpointBranch

abbrev RouteStep :=
  BEDC.Derived.RHRoute.RouteClosureSeparation.RouteStep

abbrev RouteClosureCert :=
  BEDC.Derived.RHRoute.RouteClosureSeparation.RouteClosureCert

abbrev TowerTraceEvent :=
  BEDC.Derived.RHRoute.RecursiveTower.TraceEvent

/--
一个有限 parity closure 层必须同时给出三类核验行:
层宇称等于递归深度宇称、有限路由列表显式关闭该深度目标、endpoint
dyadic 单元以同一深度作为精度。这里没有拓扑闭包或 zeta 零点声明。
-/
structure ParityClosureLayerCertificate
    {signature : RHFreeZeroSignature} {p : TowerParity}
    (tower : RecursiveParityTower signature p) where
  routeSteps : List RouteStep
  endpoint : EndpointDyadicInterval
  parity_matches_depth : p = natParity (RecursiveParityTower.depth tower)
  route_closes_depth : RouteClosureCert
    (RecursiveParityTower.depth tower) routeSteps
  endpoint_contract : EndpointDyadicDiameterContract endpoint
    (RecursiveParityTower.depth tower)

namespace ParityClosureLayerCertificate

def routeDecision
    {signature : RHFreeZeroSignature} {p : TowerParity}
    {tower : RecursiveParityTower signature p}
    (row : ParityClosureLayerCertificate tower) : Bool :=
  routeClosureDecide (RecursiveParityTower.depth tower) row.routeSteps

theorem routeDecision_sound
    {signature : RHFreeZeroSignature} {p : TowerParity}
    {tower : RecursiveParityTower signature p}
    (row : ParityClosureLayerCertificate tower) :
    row.routeDecision = true := by
  exact routeClosureDecide_of_cert row.route_closes_depth

theorem endpoint_depth
    {signature : RHFreeZeroSignature} {p : TowerParity}
    {tower : RecursiveParityTower signature p}
    (row : ParityClosureLayerCertificate tower) :
    row.endpoint.depth = RecursiveParityTower.depth tower :=
  row.endpoint_contract.left

theorem endpoint_width_num_one
    {signature : RHFreeZeroSignature} {p : TowerParity}
    {tower : RecursiveParityTower signature p}
    (row : ParityClosureLayerCertificate tower) :
    row.endpoint.hiNum = row.endpoint.loNum + 1 :=
  row.endpoint_contract.right

theorem parity_sound
    {signature : RHFreeZeroSignature} {p : TowerParity}
    {tower : RecursiveParityTower signature p}
    (row : ParityClosureLayerCertificate tower) :
    p = natParity (RecursiveParityTower.depth tower) :=
  row.parity_matches_depth

end ParityClosureLayerCertificate

def canonicalRouteSteps (target : Nat) : List RouteStep :=
  [RouteStep.closeTarget target]

theorem canonicalRouteSteps_closes (target : Nat) :
    RouteClosureCert target (canonicalRouteSteps target) := by
  exact RouteClosureCert.here []

def canonicalEndpoint
    (choose : Nat -> EndpointBranch) (precision : Nat) :
    EndpointDyadicInterval :=
  endpointReplayByFuelCell choose precision

theorem canonicalEndpoint_contract
    (choose : Nat -> EndpointBranch) (precision : Nat) :
    EndpointDyadicDiameterContract
      (canonicalEndpoint choose precision) precision := by
  exact endpointReplayByFuelCell_diameter_contract choose precision

def canonicalLayerCertificate
    {signature : RHFreeZeroSignature} {p : TowerParity}
    (choose : Nat -> EndpointBranch)
    (tower : RecursiveParityTower signature p) :
    ParityClosureLayerCertificate tower where
  routeSteps := canonicalRouteSteps (RecursiveParityTower.depth tower)
  endpoint := canonicalEndpoint choose (RecursiveParityTower.depth tower)
  parity_matches_depth := RecursiveParityTower.depth_parity tower
  route_closes_depth :=
    canonicalRouteSteps_closes (RecursiveParityTower.depth tower)
  endpoint_contract :=
    canonicalEndpoint_contract choose (RecursiveParityTower.depth tower)

/--
证书的形状跟 `RecursiveParityTower` 同步: seed 层有一张 layer row,
每个 step 在已有证书外再附一张新 layer row。于是“每层核验”是构造
证书所必须的数据, 不是事后用空壳命题补出来的标记。
-/
inductive ParityClosureTowerCertificate
    {signature : RHFreeZeroSignature} :
    {p : TowerParity} -> RecursiveParityTower signature p -> Type where
  | seed (z : SpectralZeroLayer signature)
      (row :
        ParityClosureLayerCertificate
          (RecursiveParityTower.seed z)) :
      ParityClosureTowerCertificate (RecursiveParityTower.seed z)
  | step {p : TowerParity}
      (event : TowerTraceEvent)
      (prior : RecursiveParityTower signature p)
      (priorCert : ParityClosureTowerCertificate prior)
      (row :
        ParityClosureLayerCertificate
          (RecursiveParityTower.step event prior)) :
      ParityClosureTowerCertificate
        (RecursiveParityTower.step event prior)

namespace ParityClosureTowerCertificate

def terminalRow
    {signature : RHFreeZeroSignature} {p : TowerParity}
    {tower : RecursiveParityTower signature p}
    (cert : ParityClosureTowerCertificate tower) :
    ParityClosureLayerCertificate tower :=
  match cert with
  | ParityClosureTowerCertificate.seed _ row => row
  | ParityClosureTowerCertificate.step _ _ _ row => row

def routeSteps
    {signature : RHFreeZeroSignature} {p : TowerParity}
    {tower : RecursiveParityTower signature p}
    (cert : ParityClosureTowerCertificate tower) : List RouteStep :=
  cert.terminalRow.routeSteps

def endpoint
    {signature : RHFreeZeroSignature} {p : TowerParity}
    {tower : RecursiveParityTower signature p}
    (cert : ParityClosureTowerCertificate tower) :
    EndpointDyadicInterval :=
  cert.terminalRow.endpoint

def EveryLayerVerified
    {signature : RHFreeZeroSignature} :
    {p : TowerParity} ->
      (tower : RecursiveParityTower signature p) ->
        ParityClosureTowerCertificate tower -> Prop
  | _, _, ParityClosureTowerCertificate.seed z row =>
      RecursiveParityTower.LayerParityInvariant (RecursiveParityTower.seed z) ∧
        RouteClosureCert 0 row.routeSteps ∧
          row.routeDecision = true ∧
        EndpointDyadicDiameterContract row.endpoint 0
  | _, _, ParityClosureTowerCertificate.step event prior priorCert row =>
      EveryLayerVerified prior priorCert ∧
        RecursiveParityTower.LayerParityInvariant
          (RecursiveParityTower.step event prior) ∧
          RouteClosureCert
            (RecursiveParityTower.depth (RecursiveParityTower.step event prior))
            row.routeSteps ∧
            row.routeDecision = true ∧
              EndpointDyadicDiameterContract row.endpoint
                (Nat.succ (RecursiveParityTower.depth prior))

theorem everyLayerVerified
    {signature : RHFreeZeroSignature} {p : TowerParity}
    {tower : RecursiveParityTower signature p}
    (cert : ParityClosureTowerCertificate tower) :
    EveryLayerVerified tower cert := by
  induction cert with
  | seed z row =>
      constructor
      · exact row.parity_matches_depth
      · constructor
        · exact row.route_closes_depth
        · constructor
          · exact row.routeDecision_sound
          · exact row.endpoint_contract
  | step event prior priorCert row ih =>
      constructor
      · exact ih
      · constructor
        · exact row.parity_matches_depth
        · constructor
          · exact row.route_closes_depth
          · constructor
            · exact row.routeDecision_sound
            · exact row.endpoint_contract

theorem terminal_parity
    {signature : RHFreeZeroSignature} {p : TowerParity}
    {tower : RecursiveParityTower signature p}
    (cert : ParityClosureTowerCertificate tower) :
    p = natParity (RecursiveParityTower.depth tower) :=
  cert.terminalRow.parity_sound

theorem terminal_route_decides
    {signature : RHFreeZeroSignature} {p : TowerParity}
    {tower : RecursiveParityTower signature p}
    (cert : ParityClosureTowerCertificate tower) :
    routeClosureDecide
      (RecursiveParityTower.depth tower) cert.routeSteps = true :=
  cert.terminalRow.routeDecision_sound

theorem terminal_route_closes_depth
    {signature : RHFreeZeroSignature} {p : TowerParity}
    {tower : RecursiveParityTower signature p}
    (cert : ParityClosureTowerCertificate tower) :
    RouteClosureCert
      (RecursiveParityTower.depth tower) cert.routeSteps :=
  cert.terminalRow.route_closes_depth

theorem terminal_endpoint_contract
    {signature : RHFreeZeroSignature} {p : TowerParity}
    {tower : RecursiveParityTower signature p}
    (cert : ParityClosureTowerCertificate tower) :
    EndpointDyadicDiameterContract cert.endpoint
      (RecursiveParityTower.depth tower) :=
  cert.terminalRow.endpoint_contract

theorem terminal_endpoint_depth
    {signature : RHFreeZeroSignature} {p : TowerParity}
    {tower : RecursiveParityTower signature p}
    (cert : ParityClosureTowerCertificate tower) :
    cert.endpoint.depth = RecursiveParityTower.depth tower :=
  cert.terminalRow.endpoint_depth

theorem terminal_endpoint_width_num_one
    {signature : RHFreeZeroSignature} {p : TowerParity}
    {tower : RecursiveParityTower signature p}
    (cert : ParityClosureTowerCertificate tower) :
    cert.endpoint.hiNum = cert.endpoint.loNum + 1 :=
  cert.terminalRow.endpoint_width_num_one

theorem terminal_top_trace_sound
    {signature : RHFreeZeroSignature} {p : TowerParity}
    {tower : RecursiveParityTower signature p}
    (_cert : ParityClosureTowerCertificate tower) :
    layerTrace (RecursiveParityTower.top tower) =
      RecursiveParityTower.fullTrace tower :=
  RecursiveParityTower.fullTrace_sound tower

def buildCanonical
    {signature : RHFreeZeroSignature}
    (choose : Nat -> EndpointBranch) :
    {p : TowerParity} ->
      (tower : RecursiveParityTower signature p) ->
        ParityClosureTowerCertificate tower
  | _, RecursiveParityTower.seed z =>
      ParityClosureTowerCertificate.seed z
        (canonicalLayerCertificate choose (RecursiveParityTower.seed z))
  | _, RecursiveParityTower.step event prior =>
      ParityClosureTowerCertificate.step event prior
        (buildCanonical choose prior)
        (canonicalLayerCertificate choose
          (RecursiveParityTower.step event prior))

theorem buildCanonical_everyLayerVerified
    {signature : RHFreeZeroSignature}
    (choose : Nat -> EndpointBranch)
    {p : TowerParity}
    (tower : RecursiveParityTower signature p) :
    EveryLayerVerified tower (buildCanonical choose tower) := by
  exact everyLayerVerified (buildCanonical choose tower)

end ParityClosureTowerCertificate

structure ParityClosureTowerInvariant
    {signature : RHFreeZeroSignature} {p : TowerParity}
    (tower : RecursiveParityTower signature p)
    (cert : ParityClosureTowerCertificate tower) where
  every_layer_verified :
    ParityClosureTowerCertificate.EveryLayerVerified tower cert
  terminal_parity :
    p = natParity (RecursiveParityTower.depth tower)
  terminal_route_closure :
    RouteClosureCert
      (RecursiveParityTower.depth tower)
      (ParityClosureTowerCertificate.routeSteps cert)
  terminal_endpoint_contract :
    EndpointDyadicDiameterContract
      (ParityClosureTowerCertificate.endpoint cert)
      (RecursiveParityTower.depth tower)
  top_trace_sound :
    layerTrace (RecursiveParityTower.top tower) =
      RecursiveParityTower.fullTrace tower

theorem finiteParityClosureTowerInvariant
    {signature : RHFreeZeroSignature} {p : TowerParity}
    {tower : RecursiveParityTower signature p}
    (cert : ParityClosureTowerCertificate tower) :
    ParityClosureTowerInvariant tower cert := by
  constructor
  · exact ParityClosureTowerCertificate.everyLayerVerified cert
  · exact ParityClosureTowerCertificate.terminal_parity cert
  · exact ParityClosureTowerCertificate.terminal_route_closes_depth cert
  · exact ParityClosureTowerCertificate.terminal_endpoint_contract cert
  · exact ParityClosureTowerCertificate.terminal_top_trace_sound cert

/--
无限 packet/topological closure 仍是边界接口。字段只是待构造的行,
本模块不从这些字段推出 RH, 也不构造 zeta-specific active packet。
-/
structure ParityClosureBridgeBoundary where
  activeCapture : Prop
  defectInvariant : Prop
  parityClosure : Prop
  zeroCompatibleBound : Prop

def parityClosureBridgeObligations
    (rows : ParityClosureBridgeBoundary) : Prop :=
  rows.activeCapture ∧
    rows.defectInvariant ∧
      rows.parityClosure ∧
        rows.zeroCompatibleBound

end BEDC.Derived.RHRoute.ParityClosureTowerCertificate
