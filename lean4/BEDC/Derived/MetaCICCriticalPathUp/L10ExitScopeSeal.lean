import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathL10ExitScopeSeal [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName exitSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont route localName exitSeal →
        PkgSig bundle exitSeal pkg →
          UnaryHistory route ∧ UnaryHistory localName ∧ UnaryHistory exitSeal ∧
            Cont route localName exitSeal ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle exitSeal pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro packet routeLocalNameExit exitSealPkg
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _handoffUnary,
    _dischargeSocketUnary, _transportUnary, routeUnary, _provenanceUnary, localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have exitSealUnary : UnaryHistory exitSeal :=
    unary_cont_closed routeUnary localNameUnary routeLocalNameExit
  exact
    ⟨routeUnary, localNameUnary, exitSealUnary, routeLocalNameExit, provenancePkg,
      exitSealPkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
