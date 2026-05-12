import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.TrieUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def TrieSourcePacket [AskSetup] [PackageSetup]
    (key payload depth branch provenance route payloadRoute branchRoute : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory key ∧ UnaryHistory payload ∧ UnaryHistory depth ∧ UnaryHistory branch ∧
    UnaryHistory provenance ∧ Cont key depth route ∧ Cont route branch provenance ∧
      Cont payload depth payloadRoute ∧ Cont branch payloadRoute branchRoute ∧
        PkgSig bundle provenance pkg

theorem TrieSourcePacket_carrier_stability [AskSetup] [PackageSetup]
    {key payload depth branch provenance route payloadRoute branchRoute key' payload' depth'
      branch' provenance' route' payloadRoute' branchRoute' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TrieSourcePacket key payload depth branch provenance route payloadRoute branchRoute
        bundle pkg ->
      hsame key key' ->
        hsame payload payload' ->
          hsame depth depth' ->
            hsame branch branch' ->
              Cont key' depth' route' ->
                Cont route' branch' provenance' ->
                  Cont payload' depth' payloadRoute' ->
                    Cont branch' payloadRoute' branchRoute' ->
                      PkgSig bundle provenance' pkg ->
                        TrieSourcePacket key' payload' depth' branch' provenance' route'
                            payloadRoute' branchRoute' bundle pkg ∧
                          hsame route route' ∧ hsame provenance provenance' ∧
                            hsame payloadRoute payloadRoute' ∧
                              hsame branchRoute branchRoute' := by
  intro packet sameKey samePayload sameDepth sameBranch routeRow' provenanceRow'
    payloadRouteRow' branchRouteRow' pkgRow'
  obtain ⟨keyUnary, payloadUnary, depthUnary, branchUnary, provenanceUnary, routeRow,
    provenanceRow, payloadRouteRow, branchRouteRow, _pkgRow⟩ := packet
  have sameRoute : hsame route route' :=
    cont_respects_hsame sameKey sameDepth routeRow routeRow'
  have sameProvenanceFromRoutes : hsame provenance provenance' :=
    cont_respects_hsame sameRoute sameBranch provenanceRow provenanceRow'
  have samePayloadRoute : hsame payloadRoute payloadRoute' :=
    cont_respects_hsame samePayload sameDepth payloadRouteRow payloadRouteRow'
  have sameBranchRoute : hsame branchRoute branchRoute' :=
    cont_respects_hsame sameBranch samePayloadRoute branchRouteRow branchRouteRow'
  have keyUnary' : UnaryHistory key' :=
    unary_transport keyUnary sameKey
  have payloadUnary' : UnaryHistory payload' :=
    unary_transport payloadUnary samePayload
  have depthUnary' : UnaryHistory depth' :=
    unary_transport depthUnary sameDepth
  have branchUnary' : UnaryHistory branch' :=
    unary_transport branchUnary sameBranch
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenanceFromRoutes
  exact
    ⟨⟨keyUnary', payloadUnary', depthUnary', branchUnary', provenanceUnary', routeRow',
        provenanceRow', payloadRouteRow', branchRouteRow', pkgRow'⟩,
      sameRoute, sameProvenanceFromRoutes, samePayloadRoute, sameBranchRoute⟩

def TriePacket [AskSetup] [PackageSetup]
    (key payload depth branch provenance keyPayloadRoute branchRoute endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory key ∧ UnaryHistory payload ∧ UnaryHistory depth ∧ UnaryHistory branch ∧
    Cont key payload keyPayloadRoute ∧ Cont keyPayloadRoute branch branchRoute ∧
      Cont branchRoute depth endpoint ∧ PkgSig bundle endpoint pkg

theorem TriePacket_carrier_stability [AskSetup] [PackageSetup]
    {key payload depth branch provenance keyPayloadRoute branchRoute endpoint key' payload'
      depth' branch' provenance' keyPayloadRoute' branchRoute' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TriePacket key payload depth branch provenance keyPayloadRoute branchRoute endpoint
        bundle pkg ->
      hsame key key' ->
        hsame payload payload' ->
          hsame depth depth' ->
            hsame branch branch' ->
              Cont key' payload' keyPayloadRoute' ->
                Cont keyPayloadRoute' branch' branchRoute' ->
                  Cont branchRoute' depth' endpoint' ->
                    PkgSig bundle endpoint' pkg ->
                      TriePacket key' payload' depth' branch' provenance' keyPayloadRoute'
                          branchRoute' endpoint' bundle pkg ∧
                        hsame keyPayloadRoute keyPayloadRoute' ∧
                          hsame branchRoute branchRoute' ∧ hsame endpoint endpoint' := by
  intro packet sameKey samePayload sameDepth sameBranch hKeyPayload hBranchRoute hEndpoint hPkg
  have keyPayloadSame : hsame keyPayloadRoute keyPayloadRoute' :=
    cont_respects_hsame sameKey samePayload packet.right.right.right.right.left hKeyPayload
  have branchRouteSame : hsame branchRoute branchRoute' :=
    cont_respects_hsame keyPayloadSame sameBranch packet.right.right.right.right.right.left
      hBranchRoute
  have endpointSame : hsame endpoint endpoint' :=
    cont_respects_hsame branchRouteSame sameDepth packet.right.right.right.right.right.right.left
      hEndpoint
  constructor
  · exact
      And.intro (unary_transport packet.left sameKey)
        (And.intro (unary_transport packet.right.left samePayload)
            (And.intro (unary_transport packet.right.right.left sameDepth)
              (And.intro (unary_transport packet.right.right.right.left sameBranch)
              (And.intro hKeyPayload
                (And.intro hBranchRoute (And.intro hEndpoint hPkg))))))
  · exact And.intro keyPayloadSame (And.intro branchRouteSame endpointSame)

def TrieBHistSource [AskSetup] [PackageSetup]
    (key payload depth branch provenance keyBranch payloadRoute endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory key ∧ UnaryHistory payload ∧ UnaryHistory depth ∧ UnaryHistory branch ∧
    UnaryHistory provenance ∧ Cont key branch keyBranch ∧ Cont keyBranch payload payloadRoute ∧
      Cont payloadRoute depth endpoint ∧ PkgSig bundle provenance pkg

theorem TrieBHistSource_carrier_stability [AskSetup] [PackageSetup]
    {key payload depth branch provenance keyBranch payloadRoute endpoint
      key' payload' depth' branch' provenance' keyBranch' payloadRoute' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TrieBHistSource key payload depth branch provenance keyBranch payloadRoute endpoint bundle pkg ->
      hsame key key' -> hsame payload payload' -> hsame depth depth' ->
        hsame branch branch' -> hsame provenance provenance' ->
          Cont key' branch' keyBranch' -> Cont keyBranch' payload' payloadRoute' ->
            Cont payloadRoute' depth' endpoint' -> PkgSig bundle provenance' pkg ->
              TrieBHistSource key' payload' depth' branch' provenance' keyBranch' payloadRoute'
                  endpoint' bundle pkg ∧
                hsame keyBranch keyBranch' ∧ hsame payloadRoute payloadRoute' ∧
                  hsame endpoint endpoint' := by
  intro source sameKey samePayload sameDepth sameBranch sameProvenance keyBranchRow'
    payloadRouteRow' endpointRow' pkgSig'
  obtain ⟨keyUnary, payloadUnary, depthUnary, branchUnary, provenanceUnary, keyBranchRow,
    payloadRouteRow, endpointRow, _pkgSig⟩ := source
  have sameKeyBranch : hsame keyBranch keyBranch' :=
    cont_respects_hsame sameKey sameBranch keyBranchRow keyBranchRow'
  have samePayloadRoute : hsame payloadRoute payloadRoute' :=
    cont_respects_hsame sameKeyBranch samePayload payloadRouteRow payloadRouteRow'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame samePayloadRoute sameDepth endpointRow endpointRow'
  have transported :
      TrieBHistSource key' payload' depth' branch' provenance' keyBranch' payloadRoute'
        endpoint' bundle pkg :=
    ⟨unary_transport keyUnary sameKey,
      unary_transport payloadUnary samePayload,
      unary_transport depthUnary sameDepth,
      unary_transport branchUnary sameBranch,
      unary_transport provenanceUnary sameProvenance,
      keyBranchRow',
      payloadRouteRow',
      endpointRow',
      pkgSig'⟩
  exact ⟨transported, sameKeyBranch, samePayloadRoute, sameEndpoint⟩

end BEDC.Derived.TrieUp
