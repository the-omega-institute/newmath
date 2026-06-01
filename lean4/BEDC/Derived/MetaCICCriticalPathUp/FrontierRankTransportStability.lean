import BEDC.Derived.MetaCICCriticalPathUp.FrontierRankOpenNode
import BEDC.FKernel.Cont.Cancellation

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathFrontierRankTransportStability [AskSetup] [PackageSetup]
    {openNode readyRank downstreamRank obstructionLedger replayRead provenance localName
      openNode' readyRank' downstreamRank' obstructionLedger' replayRead' provenance'
      localName' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathFrontierRankCarrier openNode readyRank downstreamRank
        obstructionLedger replayRead provenance localName bundle pkg →
      hsame openNode' openNode →
        hsame readyRank' readyRank →
          hsame downstreamRank' downstreamRank →
            hsame obstructionLedger' obstructionLedger →
              hsame replayRead' replayRead →
                hsame provenance' provenance →
                  hsame localName' localName →
                    PkgSig bundle provenance' pkg →
                      PkgSig bundle localName' pkg →
                        MetaCICCriticalPathFrontierRankCarrier openNode' readyRank'
                          downstreamRank' obstructionLedger' replayRead' provenance'
                          localName' bundle pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle hsame UnaryHistory
  intro frontierRank sameOpen sameReady sameDownstream sameObstruction sameReplay
    sameProvenance sameLocalName provenancePkg' localNamePkg'
  obtain ⟨openUnary, readyUnary, downstreamUnary, obstructionUnary, replayUnary,
    provenanceUnary, localNameUnary, openReadyDownstream, obstructionReplayLocal,
    _provenancePkg, _localNamePkg⟩ := frontierRank
  exact
    ⟨unary_transport openUnary (hsame_symm sameOpen),
      unary_transport readyUnary (hsame_symm sameReady),
      unary_transport downstreamUnary (hsame_symm sameDownstream),
      unary_transport obstructionUnary (hsame_symm sameObstruction),
      unary_transport replayUnary (hsame_symm sameReplay),
      unary_transport provenanceUnary (hsame_symm sameProvenance),
      unary_transport localNameUnary (hsame_symm sameLocalName),
      cont_hsame_transport (hsame_symm sameOpen) (hsame_symm sameReady)
        (hsame_symm sameDownstream) openReadyDownstream,
      cont_hsame_transport (hsame_symm sameObstruction) (hsame_symm sameReplay)
        (hsame_symm sameLocalName) obstructionReplayLocal,
      provenancePkg',
      localNamePkg'⟩

end BEDC.Derived.MetaCICCriticalPathUp
