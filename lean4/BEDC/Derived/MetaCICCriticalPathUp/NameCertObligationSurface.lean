import BEDC.Derived.MetaCICCriticalPathUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathPacket_namecert_obligation_surface [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket transport
        route provenance localName bundle pkg ->
      Cont route localName endpoint ->
        PkgSig bundle endpoint pkg ->
          SemanticNameCert
            (fun row : BHist =>
              MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
                  transport route provenance localName bundle pkg ∧
                hsame row endpoint)
            (fun row : BHist =>
              Cont strongNorm normalForm route ∧ Cont handoff obstruction dischargeSocket ∧
                Cont route localName row ∧ PkgSig bundle provenance pkg)
            (fun row : BHist => UnaryHistory row ∧ PkgSig bundle endpoint pkg) hsame := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle Pkg SemanticNameCert
  intro packet routeLocalNameEndpoint endpointPkg
  have packetWitness := packet
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _handoffUnary,
    _dischargeSocketUnary, _transportUnary, routeUnary, _provenanceUnary, localNameUnary,
    strongNormNormalFormRoute, handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed routeUnary localNameUnary routeLocalNameEndpoint
  exact {
    core := {
      carrier_inhabited := Exists.intro endpoint (And.intro packetWitness (hsame_refl endpoint))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro row source
      exact
        ⟨strongNormNormalFormRoute, handoffObstructionSocket,
          cont_result_hsame_transport routeLocalNameEndpoint (hsame_symm source.right),
          provenancePkg⟩
    ledger_sound := by
      intro row source
      exact And.intro (unary_transport endpointUnary (hsame_symm source.right)) endpointPkg
  }

end BEDC.Derived.MetaCICCriticalPathUp
