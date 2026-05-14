import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ZnormalPacket [AskSetup] [PackageSetup]
    (typed fuel terminal normal continuation transports routes provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory
  UnaryHistory typed ∧ UnaryHistory fuel ∧ UnaryHistory terminal ∧
    UnaryHistory normal ∧ UnaryHistory continuation ∧ UnaryHistory transports ∧
      UnaryHistory routes ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
        Cont typed fuel terminal ∧ Cont terminal normal continuation ∧
          Cont continuation transports routes ∧ PkgSig bundle name pkg ∧
            PkgSig bundle provenance pkg

theorem ZnormalPacket_sibling_normalword_handoff [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name handoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      UnaryHistory normal →
        Cont normal continuation handoff →
          UnaryHistory handoff ∧ hsame handoff (append normal continuation) ∧
            PkgSig bundle name pkg ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet normalUnary normalContinuationHandoff
  obtain ⟨_typedUnary, _fuelUnary, _terminalUnary, _normalUnary, continuationUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, _typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, namePkg, provenancePkg⟩ :=
    packet
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed normalUnary continuationUnary normalContinuationHandoff
  exact ⟨handoffUnary, normalContinuationHandoff, namePkg, provenancePkg⟩

end BEDC.Derived.ZnormalUp
