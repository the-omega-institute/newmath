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

theorem TrieSourcePacket_key_path_route_exhaustion [AskSetup] [PackageSetup]
    {key payload depth branch provenance route payloadRoute branchRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TrieSourcePacket key payload depth branch provenance route payloadRoute branchRoute bundle pkg →
      UnaryHistory route ∧ UnaryHistory payloadRoute ∧ UnaryHistory branchRoute ∧
        UnaryHistory provenance ∧ Cont key depth route ∧ Cont route branch provenance ∧
          PkgSig bundle provenance pkg := by
  intro packet
  obtain ⟨keyUnary, payloadUnary, depthUnary, branchUnary, provenanceUnary, routeRow,
    provenanceRow, payloadRouteRow, branchRouteRow, pkgRow⟩ := packet
  have routeUnary : UnaryHistory route :=
    unary_cont_closed keyUnary depthUnary routeRow
  have payloadRouteUnary : UnaryHistory payloadRoute :=
    unary_cont_closed payloadUnary depthUnary payloadRouteRow
  have branchRouteUnary : UnaryHistory branchRoute :=
    unary_cont_closed branchUnary payloadRouteUnary branchRouteRow
  exact
    ⟨routeUnary, payloadRouteUnary, branchRouteUnary, provenanceUnary, routeRow,
      provenanceRow, pkgRow⟩

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

theorem TrieSourcePacket_branch_read_exactness [AskSetup] [PackageSetup]
    {key payload depth branch provenance route payloadRoute branchRoute pref branchTag readback
      : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TrieSourcePacket key payload depth branch provenance route payloadRoute branchRoute
        bundle pkg ->
      Cont pref branchTag readback ->
        UnaryHistory pref ->
          UnaryHistory branchTag ->
            PkgSig bundle provenance pkg ->
              (pref = BHist.Empty ∨
                  ∃ tail : BHist, pref = BHist.e1 tail ∧ UnaryHistory tail) ∧
                UnaryHistory readback ∧ UnaryHistory key ∧ UnaryHistory branch ∧
                  UnaryHistory depth ∧ Cont pref branchTag readback ∧
                    PkgSig bundle provenance pkg := by
  intro packet branchRead prefUnary branchTagUnary provenancePkg
  obtain ⟨keyUnary, _payloadUnary, depthUnary, branchUnary, _provenanceUnary,
    _routeRow, _provenanceRow, _payloadRouteRow, _branchRouteRow, _packetPkg⟩ := packet
  have prefSplit :
      pref = BHist.Empty ∨ ∃ tail : BHist, pref = BHist.e1 tail ∧ UnaryHistory tail :=
    unary_history_empty_or_e1_tail prefUnary
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed prefUnary branchTagUnary branchRead
  exact
    ⟨prefSplit, readbackUnary, keyUnary, branchUnary, depthUnary, branchRead,
      provenancePkg⟩

theorem TriePrefixExtensionClassifier_stability [AskSetup] [PackageSetup]
    {pre pre' branch ext ext' prov : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory pre -> UnaryHistory branch -> hsame pre pre' -> Cont pre branch ext ->
      Cont pre' branch ext' -> PkgSig bundle prov pkg ->
        UnaryHistory pre' ∧ UnaryHistory ext ∧ UnaryHistory ext' ∧ hsame ext ext' ∧
          PkgSig bundle prov pkg := by
  intro preUnary branchUnary samePrefix extRow extRow' pkgSig
  have preUnary' : UnaryHistory pre' :=
    unary_transport preUnary samePrefix
  have extUnary : UnaryHistory ext :=
    unary_cont_closed preUnary branchUnary extRow
  have extUnary' : UnaryHistory ext' :=
    unary_cont_closed preUnary' branchUnary extRow'
  have sameExt : hsame ext ext' :=
    cont_respects_hsame samePrefix (hsame_refl branch) extRow extRow'
  exact And.intro preUnary'
    (And.intro extUnary
      (And.intro extUnary'
        (And.intro sameExt pkgSig)))

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

theorem TrieBHistSource_lookup_ledger_exhaustion [AskSetup] [PackageSetup]
    {key payload depth branch provenance keyBranch payloadRoute endpoint lookup consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TrieBHistSource key payload depth branch provenance keyBranch payloadRoute endpoint
        bundle pkg ->
      UnaryHistory lookup ->
        Cont endpoint lookup consumer ->
          PkgSig bundle consumer pkg ->
            UnaryHistory key ∧ UnaryHistory payload ∧ UnaryHistory depth ∧
              UnaryHistory branch ∧ UnaryHistory provenance ∧ UnaryHistory keyBranch ∧
                UnaryHistory payloadRoute ∧ UnaryHistory endpoint ∧ UnaryHistory consumer ∧
                  Cont key branch keyBranch ∧ Cont keyBranch payload payloadRoute ∧
                    Cont payloadRoute depth endpoint ∧ Cont endpoint lookup consumer ∧
                      PkgSig bundle consumer pkg := by
  intro source lookupUnary lookupRow consumerPkg
  obtain ⟨keyUnary, payloadUnary, depthUnary, branchUnary, provenanceUnary, keyBranchRow,
    payloadRouteRow, endpointRow, _provenancePkg⟩ := source
  have keyBranchUnary : UnaryHistory keyBranch :=
    unary_cont_closed keyUnary branchUnary keyBranchRow
  have payloadRouteUnary : UnaryHistory payloadRoute :=
    unary_cont_closed keyBranchUnary payloadUnary payloadRouteRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed payloadRouteUnary depthUnary endpointRow
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed endpointUnary lookupUnary lookupRow
  exact
    ⟨keyUnary, payloadUnary, depthUnary, branchUnary, provenanceUnary, keyBranchUnary,
      payloadRouteUnary, endpointUnary, consumerUnary, keyBranchRow, payloadRouteRow,
      endpointRow, lookupRow, consumerPkg⟩

def TrieSource [AskSetup] [PackageSetup]
    (key value depth branch provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory key ∧ UnaryHistory value ∧ UnaryHistory depth ∧ UnaryHistory branch ∧
    Cont key value endpoint ∧ Cont depth branch provenance ∧ PkgSig bundle provenance pkg

theorem TrieSource_carrier_stability [AskSetup] [PackageSetup]
    {key value depth branch provenance endpoint key' value' depth' branch' provenance'
      endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TrieSource key value depth branch provenance endpoint bundle pkg ->
      hsame key key' ->
        hsame value value' ->
          hsame depth depth' ->
            hsame branch branch' ->
              Cont key' value' endpoint' ->
                Cont depth' branch' provenance' ->
                  PkgSig bundle provenance' pkg ->
                    TrieSource key' value' depth' branch' provenance' endpoint' bundle pkg ∧
                      hsame endpoint endpoint' ∧ hsame provenance provenance' := by
  intro source sameKey sameValue sameDepth sameBranch endpointRow' provenanceRow' pkgRow'
  obtain ⟨keyUnary, valueUnary, depthUnary, branchUnary, endpointRow, provenanceRow,
    _pkgRow⟩ := source
  have endpointSame : hsame endpoint endpoint' :=
    cont_respects_hsame sameKey sameValue endpointRow endpointRow'
  have provenanceSame : hsame provenance provenance' :=
    cont_respects_hsame sameDepth sameBranch provenanceRow provenanceRow'
  have keyUnary' : UnaryHistory key' :=
    unary_transport keyUnary sameKey
  have valueUnary' : UnaryHistory value' :=
    unary_transport valueUnary sameValue
  have depthUnary' : UnaryHistory depth' :=
    unary_transport depthUnary sameDepth
  have branchUnary' : UnaryHistory branch' :=
    unary_transport branchUnary sameBranch
  exact
    ⟨⟨keyUnary', valueUnary', depthUnary', branchUnary', endpointRow', provenanceRow',
        pkgRow'⟩,
      endpointSame, provenanceSame⟩

def TrieTerminalPacket [AskSetup] [PackageSetup]
    (key terminal transport route branch provenance cert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory key ∧ UnaryHistory terminal ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
    Cont key terminal transport ∧ Cont transport route branch ∧ Cont branch provenance cert ∧
      PkgSig bundle cert pkg

theorem TrieTerminalPacket_boolean_key_path_ledger_coverage [AskSetup] [PackageSetup]
    {key terminal transport route branch provenance cert key' terminal' transport' route' branch'
      provenance' cert' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TrieTerminalPacket key terminal transport route branch provenance cert bundle pkg ->
      TrieTerminalPacket key' terminal' transport' route' branch' provenance' cert' bundle pkg ->
        hsame key key' ->
          hsame terminal terminal' ->
            hsame route route' ->
              hsame provenance provenance' ->
                  hsame transport transport' ∧ hsame branch branch' ∧ hsame cert cert' := by
    intro packet packet' sameKey sameTerminal sameRoute sameProvenance
    obtain ⟨_keyUnary, _terminalUnary, _routeUnary, _provenanceUnary, transportRow,
      branchRow, certRow, _pkgSig⟩ := packet
    obtain ⟨_keyUnary', _terminalUnary', _routeUnary', _provenanceUnary', transportRow',
      branchRow', certRow', _pkgSig'⟩ := packet'
    have sameTransport : hsame transport transport' :=
      cont_respects_hsame sameKey sameTerminal transportRow transportRow'
    have sameBranch : hsame branch branch' :=
      cont_respects_hsame sameTransport sameRoute branchRow branchRow'
    have sameCert : hsame cert cert' :=
      cont_respects_hsame sameBranch sameProvenance certRow certRow'
    exact ⟨sameTransport, sameBranch, sameCert⟩

theorem TrieBranchRead_exactness [AskSetup] [PackageSetup]
    {key payload depth branch provenance branchRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory key ->
      UnaryHistory depth ->
        UnaryHistory payload ->
          UnaryHistory provenance ->
            Cont key depth branch ->
              Cont branch payload branchRead ->
                Cont branchRead provenance consumerRead ->
                  PkgSig bundle consumerRead pkg ->
                    UnaryHistory branch ∧ UnaryHistory branchRead ∧ UnaryHistory consumerRead ∧
                      hsame branch (append key depth) ∧
                        hsame branchRead (append branch payload) ∧
                          hsame consumerRead (append branchRead provenance) ∧
                            PkgSig bundle consumerRead pkg := by
  intro keyUnary depthUnary payloadUnary provenanceUnary branchRow branchReadRow consumerReadRow
    pkgSig
  have branchUnary : UnaryHistory branch :=
    unary_cont_closed keyUnary depthUnary branchRow
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed branchUnary payloadUnary branchReadRow
  have consumerReadUnary : UnaryHistory consumerRead :=
    unary_cont_closed branchReadUnary provenanceUnary consumerReadRow
  exact
    ⟨branchUnary, branchReadUnary, consumerReadUnary, branchRow, branchReadRow, consumerReadRow,
      pkgSig⟩

end BEDC.Derived.TrieUp
