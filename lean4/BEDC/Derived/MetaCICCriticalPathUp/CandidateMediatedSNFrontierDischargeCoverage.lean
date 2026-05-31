import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathCandidateMediatedSNFrontierDischargeCoverage
    [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName candidateRead frontierReplay socketRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg ->
      Cont strongNorm normalForm candidateRead ->
        Cont candidateRead handoff frontierReplay ->
          Cont handoff obstruction socketRead ->
            PkgSig bundle frontierReplay pkg ->
              PkgSig bundle socketRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row frontierReplay ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row strongNorm ∨ hsame row normalForm ∨ hsame row handoff ∨
                        hsame row dischargeSocket ∨ hsame row frontierReplay)
                    (fun row : BHist =>
                      PkgSig bundle row pkg ∧ Cont candidateRead handoff frontierReplay ∧
                        Cont handoff obstruction socketRead)
                    hsame ∧
                  UnaryHistory frontierReplay ∧ UnaryHistory socketRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet candidateRoute frontierRoute socketRoute frontierPkg _socketPkg
  obtain ⟨strongNormUnary, normalFormUnary, obstructionUnary, handoffUnary,
    _dischargeSocketUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _localNameUnary, _strongNormNormalFormRoute, _handoffObstructionSocket,
    _transportLocalName, _provenancePkg⟩ := packet
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed strongNormUnary normalFormUnary candidateRoute
  have frontierReplayUnary : UnaryHistory frontierReplay :=
    unary_cont_closed candidateReadUnary handoffUnary frontierRoute
  have socketReadUnary : UnaryHistory socketRead :=
    unary_cont_closed handoffUnary obstructionUnary socketRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row frontierReplay ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row strongNorm ∨ hsame row normalForm ∨ hsame row handoff ∨
              hsame row dischargeSocket ∨ hsame row frontierReplay)
          (fun row : BHist =>
            PkgSig bundle row pkg ∧ Cont candidateRead handoff frontierReplay ∧
              Cont handoff obstruction socketRead)
      hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro frontierReplay ⟨hsame_refl frontierReplay, frontierReplayUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro row source
      cases source.left
      exact ⟨frontierPkg, frontierRoute, socketRoute⟩
  }
  exact ⟨cert, frontierReplayUnary, socketReadUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
