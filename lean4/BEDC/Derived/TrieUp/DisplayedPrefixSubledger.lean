import BEDC.Derived.TrieUp

namespace BEDC.Derived.TrieUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TrieDisplayedPrefixSubledger_provenance_exhaustion [AskSetup] [PackageSetup]
    {key payload depth branch provenance route payloadRoute branchRoute restrictedKey
      restrictedPayload restrictedDepth restrictedBranch restrictedProvenance restrictedRoute
      restrictedPayloadRoute restrictedBranchRoute restrictedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TrieSourcePacket key payload depth branch provenance route payloadRoute branchRoute bundle pkg →
      hsame key restrictedKey →
        hsame payload restrictedPayload →
          hsame depth restrictedDepth →
            hsame branch restrictedBranch →
              Cont restrictedKey restrictedDepth restrictedRoute →
                Cont restrictedRoute restrictedBranch restrictedProvenance →
                  Cont restrictedPayload restrictedDepth restrictedPayloadRoute →
                    Cont restrictedBranch restrictedPayloadRoute restrictedBranchRoute →
                      PkgSig bundle restrictedProvenance pkg →
                        Cont restrictedProvenance restrictedPayloadRoute restrictedRead →
                          PkgSig bundle restrictedRead pkg →
                            UnaryHistory restrictedKey ∧
                              UnaryHistory restrictedPayload ∧
                                UnaryHistory restrictedDepth ∧
                                  UnaryHistory restrictedBranch ∧
                                    UnaryHistory restrictedProvenance ∧
                                      UnaryHistory restrictedRead ∧
                                        Cont restrictedProvenance restrictedPayloadRoute
                                          restrictedRead ∧
                                          PkgSig bundle restrictedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont hsame PkgSig
  intro packet sameKey samePayload sameDepth sameBranch restrictedRouteRow
    restrictedProvenanceRow restrictedPayloadRouteRow restrictedBranchRouteRow restrictedPkg
    restrictedReadRow restrictedReadPkg
  have restrictedPacket :
      TrieSourcePacket restrictedKey restrictedPayload restrictedDepth restrictedBranch
        restrictedProvenance restrictedRoute restrictedPayloadRoute restrictedBranchRoute bundle
        pkg :=
    (TrieSourcePacket_carrier_stability packet sameKey samePayload sameDepth sameBranch
      restrictedRouteRow restrictedProvenanceRow restrictedPayloadRouteRow
      restrictedBranchRouteRow restrictedPkg).left
  have coverage :=
    TrieSourcePacket_ledger_coverage restrictedPacket restrictedReadRow restrictedReadPkg
  obtain ⟨restrictedKeyUnary, restrictedPayloadUnary, restrictedDepthUnary,
    restrictedBranchUnary, restrictedProvenanceUnary, _restrictedRouteUnary,
    _restrictedPayloadRouteUnary, _restrictedBranchRouteUnary, restrictedReadUnary,
    _restrictedRouteRow, _restrictedProvenanceRow, _restrictedPayloadRouteRow,
    _restrictedBranchRouteRow, restrictedReadRowOut, restrictedReadPkgOut⟩ := coverage
  exact
    ⟨restrictedKeyUnary, restrictedPayloadUnary, restrictedDepthUnary, restrictedBranchUnary,
      restrictedProvenanceUnary, restrictedReadUnary, restrictedReadRowOut,
      restrictedReadPkgOut⟩

end BEDC.Derived.TrieUp
