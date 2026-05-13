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

end BEDC.Derived.TrieUp
