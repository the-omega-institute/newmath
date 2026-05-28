import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathPacket_root_discharge_exactness [AskSetup] [PackageSetup]
    {S N O U D H C P L dischargeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket S N O U D H C P L bundle pkg ->
      hsame dischargeRead D ->
        UnaryHistory S ∧ UnaryHistory N ∧ UnaryHistory O ∧ UnaryHistory U ∧
          UnaryHistory D ∧ UnaryHistory dischargeRead ∧ Cont U O D ∧ hsame H L ∧
            PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle Pkg UnaryHistory PkgSig
  intro packet sameDischargeRead
  obtain ⟨strongNormUnary, normalFormUnary, obstructionUnary, handoffUnary,
    dischargeSocketUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _localNameUnary, _strongNormNormalFormRoute, handoffObstructionSocket,
    transportLocalName, provenancePkg⟩ := packet
  have dischargeReadUnary : UnaryHistory dischargeRead :=
    unary_transport dischargeSocketUnary (hsame_symm sameDischargeRead)
  exact
    ⟨strongNormUnary, normalFormUnary, obstructionUnary, handoffUnary,
      dischargeSocketUnary, dischargeReadUnary, handoffObstructionSocket,
      transportLocalName, provenancePkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
