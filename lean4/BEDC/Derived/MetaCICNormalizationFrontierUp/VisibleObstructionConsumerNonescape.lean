import BEDC.Derived.MetaCICNormalizationFrontierUp.VisibleObstructionRouteFactorization
import BEDC.FKernel.Cont.Cancellation

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationFrontierVisibleObstructionConsumerNonescape
    [AskSetup] [PackageSetup]
    {candidate closedCandidate finished endpoint obstruction transport replay provenance
      localRow candidateRead endpointRead obstructionRead visibleRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationFrontierCarrier candidate closedCandidate finished endpoint
        obstruction transport replay provenance localRow bundle pkg →
      Cont candidate closedCandidate candidateRead →
        Cont finished endpoint endpointRead →
          Cont obstruction transport obstructionRead →
            Cont obstructionRead replay visibleRead →
              Cont candidateRead endpointRead publicRead →
                PkgSig bundle visibleRead pkg →
                  PkgSig bundle publicRead pkg →
                    UnaryHistory visibleRead ∧ UnaryHistory publicRead ∧
                      PkgSig bundle visibleRead pkg ∧ PkgSig bundle publicRead pkg ∧
                        hsame obstruction obstruction ∧
                          (Cont visibleRead (BHist.e0 replay) obstructionRead → False) ∧
                            (Cont publicRead (BHist.e1 endpointRead) candidateRead →
                              False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier candidateClosedRead finishedEndpointRead obstructionTransportRead
    obstructionReplayVisible candidateEndpointPublic visiblePkg publicPkg
  obtain ⟨_obstructionReadUnary, visibleReadUnary, publicReadUnary,
    _obstructionReplayVisible, _candidateEndpointPublic, visiblePkg', publicPkg'⟩ :=
    MetaCICNormalizationFrontierVisibleObstruction_route_factorization carrier
      candidateClosedRead finishedEndpointRead obstructionTransportRead obstructionReplayVisible
      candidateEndpointPublic visiblePkg publicPkg
  exact
    ⟨visibleReadUnary, publicReadUnary, visiblePkg', publicPkg', hsame_refl obstruction,
      (fun back =>
        cont_mutual_extension_right_tail_absurd.left obstructionReplayVisible back),
      (fun back =>
        cont_mutual_extension_right_tail_absurd.right candidateEndpointPublic back)⟩

end BEDC.Derived.MetaCICNormalizationFrontierUp
