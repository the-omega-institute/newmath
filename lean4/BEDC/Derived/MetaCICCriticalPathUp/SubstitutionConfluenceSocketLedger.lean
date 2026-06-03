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

theorem MetaCICCriticalPathPacket_substitution_confluence_socket_ledger [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName substConfluenceRead socketLedgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket transport
        route provenance localName bundle pkg ->
      Cont handoff obstruction substConfluenceRead ->
        Cont substConfluenceRead dischargeSocket socketLedgerRead ->
          PkgSig bundle socketLedgerRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row socketLedgerRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row handoff ∨ hsame row obstruction ∨ hsame row dischargeSocket ∨
                    hsame row socketLedgerRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle socketLedgerRead pkg ∧
                    Cont substConfluenceRead dischargeSocket socketLedgerRead)
                hsame ∧
              UnaryHistory substConfluenceRead ∧ UnaryHistory socketLedgerRead ∧
                PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle SemanticNameCert hsame UnaryHistory
  intro packet handoffObstructionRead substitutionSocketRead socketLedgerPkg
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, handoffUnary,
    dischargeSocketUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _localNameUnary, _strongNormNormalFormRoute, _handoffObstructionSocket,
    _transportLocalName, provenancePkg⟩ := packet
  have substConfluenceUnary : UnaryHistory substConfluenceRead :=
    unary_cont_closed handoffUnary obstructionUnary handoffObstructionRead
  have socketLedgerUnary : UnaryHistory socketLedgerRead :=
    unary_cont_closed substConfluenceUnary dischargeSocketUnary substitutionSocketRead
  have sourceSocketLedger :
      (fun row : BHist => hsame row socketLedgerRead ∧ UnaryHistory row) socketLedgerRead := by
    exact ⟨hsame_refl socketLedgerRead, socketLedgerUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row socketLedgerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row handoff ∨ hsame row obstruction ∨ hsame row dischargeSocket ∨
              hsame row socketLedgerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle socketLedgerRead pkg ∧
              Cont substConfluenceRead dischargeSocket socketLedgerRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro socketLedgerRead sourceSocketLedger
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
      exact Or.inr (Or.inr (Or.inr source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, socketLedgerPkg, substitutionSocketRead⟩
  }
  exact ⟨cert, substConfluenceUnary, socketLedgerUnary, provenancePkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
