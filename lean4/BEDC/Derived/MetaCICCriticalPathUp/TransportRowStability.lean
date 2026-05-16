import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathPacket_transport_row_stability [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName strongNorm' normalForm' obstruction' handoff' dischargeSocket' transport'
      route' provenance' localName' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      hsame strongNorm strongNorm' →
        hsame normalForm normalForm' →
          hsame obstruction obstruction' →
            hsame handoff handoff' →
              hsame dischargeSocket dischargeSocket' →
                hsame transport transport' →
                  hsame provenance provenance' →
                    hsame localName localName' →
                      Cont strongNorm' normalForm' route' →
                        Cont handoff' obstruction' dischargeSocket' →
                          PkgSig bundle provenance' pkg →
                            MetaCICCriticalPathPacket strongNorm' normalForm' obstruction'
                                handoff' dischargeSocket' transport' route' provenance'
                                localName' bundle pkg ∧
                              hsame route route' ∧ hsame dischargeSocket dischargeSocket' := by
  -- BEDC touchpoint anchor: BHist UnaryHistory hsame Cont ProbeBundle PkgSig
  intro packet sameStrongNorm sameNormalForm sameObstruction sameHandoff
    sameDischargeSocket sameTransport sameProvenance sameLocalName strongNormNormalFormRoute
    handoffObstructionSocket provenancePkg
  obtain ⟨strongNormUnary, normalFormUnary, obstructionUnary, handoffUnary,
    dischargeSocketUnary, transportUnary, _routeUnary, provenanceUnary, localNameUnary,
    strongNormNormalFormRoute0, _handoffObstructionSocket0, transportLocalName,
    _provenancePkg0⟩ := packet
  have routeSame : hsame route route' :=
    cont_respects_hsame sameStrongNorm sameNormalForm strongNormNormalFormRoute0
      strongNormNormalFormRoute
  have transportLocalName' : hsame transport' localName' :=
    hsame_trans (hsame_symm sameTransport) (hsame_trans transportLocalName sameLocalName)
  have packet' :
      MetaCICCriticalPathPacket strongNorm' normalForm' obstruction' handoff'
        dischargeSocket' transport' route' provenance' localName' bundle pkg :=
    ⟨unary_transport strongNormUnary sameStrongNorm,
      unary_transport normalFormUnary sameNormalForm,
      unary_transport obstructionUnary sameObstruction,
      unary_transport handoffUnary sameHandoff,
      unary_transport dischargeSocketUnary sameDischargeSocket,
      unary_transport transportUnary sameTransport,
      unary_cont_closed (unary_transport strongNormUnary sameStrongNorm)
        (unary_transport normalFormUnary sameNormalForm) strongNormNormalFormRoute,
      unary_transport provenanceUnary sameProvenance,
      unary_transport localNameUnary sameLocalName,
      strongNormNormalFormRoute, handoffObstructionSocket, transportLocalName',
      provenancePkg⟩
  exact ⟨packet', routeSame, sameDischargeSocket⟩

end BEDC.Derived.MetaCICCriticalPathUp
