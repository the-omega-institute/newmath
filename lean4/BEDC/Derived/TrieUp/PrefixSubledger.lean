import BEDC.Derived.TrieUp

namespace BEDC.Derived.TrieUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def TrieDisplayedPrefixSubledger [AskSetup] [PackageSetup]
    (key payload depth branch provenance subKey subPayload subDepth subBranch subProvenance
      inclusion : BHist) : Prop :=
  hsame subKey key ∧ hsame subPayload payload ∧ hsame subDepth depth ∧
    hsame subBranch branch ∧ hsame subProvenance provenance ∧ UnaryHistory inclusion

theorem TrieDisplayedPrefixSubledger_restriction_carrier [AskSetup] [PackageSetup]
    {key payload depth branch provenance route payloadRoute branchRoute subKey subPayload
      subDepth subBranch subProvenance inclusion subRoute subPayloadRoute
      subBranchRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TrieSourcePacket key payload depth branch provenance route payloadRoute branchRoute
        bundle pkg →
      TrieDisplayedPrefixSubledger key payload depth branch provenance subKey subPayload
        subDepth subBranch subProvenance inclusion →
        Cont subKey subDepth subRoute →
          Cont subRoute subBranch subProvenance →
            Cont subPayload subDepth subPayloadRoute →
              Cont subBranch subPayloadRoute subBranchRoute →
                PkgSig bundle subProvenance pkg →
                  TrieSourcePacket subKey subPayload subDepth subBranch subProvenance
                    subRoute subPayloadRoute subBranchRoute bundle pkg := by
  intro packet restriction subRouteRow subProvenanceRow subPayloadRouteRow subBranchRouteRow
    subPkg
  obtain ⟨keyUnary, payloadUnary, depthUnary, branchUnary, provenanceUnary, _routeRow,
    _provenanceRow, _payloadRouteRow, _branchRouteRow, _pkgRow⟩ := packet
  obtain ⟨subKeySame, subPayloadSame, subDepthSame, subBranchSame, subProvenanceSame,
    _inclusionUnary⟩ := restriction
  have subKeyUnary : UnaryHistory subKey :=
    unary_transport_symm keyUnary subKeySame
  have subPayloadUnary : UnaryHistory subPayload :=
    unary_transport_symm payloadUnary subPayloadSame
  have subDepthUnary : UnaryHistory subDepth :=
    unary_transport_symm depthUnary subDepthSame
  have subBranchUnary : UnaryHistory subBranch :=
    unary_transport_symm branchUnary subBranchSame
  have subProvenanceUnary : UnaryHistory subProvenance :=
    unary_transport_symm provenanceUnary subProvenanceSame
  exact
    ⟨subKeyUnary, subPayloadUnary, subDepthUnary, subBranchUnary, subProvenanceUnary,
      subRouteRow, subProvenanceRow, subPayloadRouteRow, subBranchRouteRow, subPkg⟩

theorem TriePrefixSubledger_provenance_exhaustion [AskSetup] [PackageSetup]
    {key payload depth branch provenance route payloadRoute branchRoute subKey subPayload
      subDepth subBranch subProvenance inclusion subRoute subPayloadRoute subBranchRoute
      consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TrieSourcePacket key payload depth branch provenance route payloadRoute branchRoute
        bundle pkg ->
      TrieDisplayedPrefixSubledger key payload depth branch provenance subKey subPayload
        subDepth subBranch subProvenance inclusion ->
        Cont subKey subDepth subRoute ->
          Cont subRoute subBranch subProvenance ->
            Cont subPayload subDepth subPayloadRoute ->
              Cont subBranch subPayloadRoute subBranchRoute ->
                Cont subProvenance subPayloadRoute consumer ->
                  PkgSig bundle subProvenance pkg ->
                    PkgSig bundle consumer pkg ->
                      UnaryHistory subKey ∧ UnaryHistory subPayload ∧
                        UnaryHistory subDepth ∧ UnaryHistory subBranch ∧
                          UnaryHistory subProvenance ∧ UnaryHistory consumer ∧
                            PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig
  intro packet restriction subRouteRow subProvenanceRow subPayloadRouteRow subBranchRouteRow
    consumerRow subPkg consumerPkg
  have restrictedPacket :
      TrieSourcePacket subKey subPayload subDepth subBranch subProvenance subRoute
        subPayloadRoute subBranchRoute bundle pkg :=
    TrieDisplayedPrefixSubledger_restriction_carrier packet restriction subRouteRow
      subProvenanceRow subPayloadRouteRow subBranchRouteRow subPkg
  have coverage :=
    TrieSourcePacket_ledger_coverage restrictedPacket consumerRow consumerPkg
  exact
    ⟨coverage.left, coverage.right.left, coverage.right.right.left,
      coverage.right.right.right.left, coverage.right.right.right.right.left,
      coverage.right.right.right.right.right.right.right.right.left,
      coverage.right.right.right.right.right.right.right.right.right.right.right.right.right.right⟩

theorem TrieDisplayedPrefixSubledger_public_read_exhaustion [AskSetup] [PackageSetup]
    {key payload depth branch provenance route payloadRoute branchRoute subKey subPayload
      subDepth subBranch subProvenance inclusion subRoute subPayloadRoute subBranchRoute
      restrictedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TrieSourcePacket key payload depth branch provenance route payloadRoute branchRoute
        bundle pkg →
      TrieDisplayedPrefixSubledger key payload depth branch provenance subKey subPayload
        subDepth subBranch subProvenance inclusion →
        Cont subKey subDepth subRoute →
          Cont subRoute subBranch subProvenance →
            Cont subPayload subDepth subPayloadRoute →
              Cont subBranch subPayloadRoute subBranchRoute →
                PkgSig bundle subProvenance pkg →
                  Cont subBranchRoute subProvenance restrictedRead →
                    PkgSig bundle restrictedRead pkg →
                      TrieSourcePacket subKey subPayload subDepth subBranch subProvenance
                          subRoute subPayloadRoute subBranchRoute bundle pkg ∧
                        UnaryHistory restrictedRead ∧
                          Cont subBranchRoute subProvenance restrictedRead ∧
                            PkgSig bundle restrictedRead pkg := by
  -- BEDC touchpoint anchor: TrieSourcePacket BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro packet restriction subRouteRow subProvenanceRow subPayloadRouteRow subBranchRouteRow
    subPkg restrictedRow restrictedPkg
  have restrictedPacket :
      TrieSourcePacket subKey subPayload subDepth subBranch subProvenance subRoute
        subPayloadRoute subBranchRoute bundle pkg :=
    TrieDisplayedPrefixSubledger_restriction_carrier packet restriction subRouteRow
      subProvenanceRow subPayloadRouteRow subBranchRouteRow subPkg
  obtain ⟨_subKeyUnary, _subPayloadUnary, _subDepthUnary, _subBranchUnary,
    subProvenanceUnary, _subRouteRow, _subProvenanceRow, _subPayloadRouteRow,
    subBranchRouteRow', _subPkg⟩ := restrictedPacket
  have subPayloadRouteUnary : UnaryHistory subPayloadRoute :=
    unary_cont_closed _subPayloadUnary _subDepthUnary _subPayloadRouteRow
  have subBranchRouteUnary : UnaryHistory subBranchRoute :=
    unary_cont_closed _subBranchUnary subPayloadRouteUnary subBranchRouteRow'
  have restrictedUnary : UnaryHistory restrictedRead :=
    unary_cont_closed subBranchRouteUnary subProvenanceUnary restrictedRow
  exact
    ⟨⟨_subKeyUnary, _subPayloadUnary, _subDepthUnary, _subBranchUnary,
      subProvenanceUnary, _subRouteRow, _subProvenanceRow, _subPayloadRouteRow,
      subBranchRouteRow', _subPkg⟩, restrictedUnary, restrictedRow, restrictedPkg⟩

end BEDC.Derived.TrieUp
