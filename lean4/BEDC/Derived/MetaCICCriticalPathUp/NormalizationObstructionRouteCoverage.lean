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

theorem MetaCICCriticalPathPacket_normalization_obstruction_route_coverage
    [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName budget schedule readback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg ->
      Cont route localName budget ->
        Cont budget route schedule ->
          Cont schedule normalForm readback ->
            PkgSig bundle readback pkg ->
              UnaryHistory obstruction ∧ UnaryHistory route ∧ UnaryHistory budget ∧
                UnaryHistory schedule ∧ UnaryHistory readback ∧
                  Cont strongNorm normalForm route ∧ Cont route localName budget ∧
                    Cont budget route schedule ∧ Cont schedule normalForm readback ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle readback pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet routeLocalNameBudget budgetRouteSchedule scheduleNormalFormReadback
    readbackPkg
  obtain ⟨_strongNormUnary, normalFormUnary, obstructionUnary, _handoffUnary,
    _dischargeSocketUnary, _transportUnary, routeUnary, _provenanceUnary, localNameUnary,
    strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have budgetUnary : UnaryHistory budget :=
    unary_cont_closed routeUnary localNameUnary routeLocalNameBudget
  have scheduleUnary : UnaryHistory schedule :=
    unary_cont_closed budgetUnary routeUnary budgetRouteSchedule
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed scheduleUnary normalFormUnary scheduleNormalFormReadback
  exact
    ⟨obstructionUnary, routeUnary, budgetUnary, scheduleUnary, readbackUnary,
      strongNormNormalFormRoute, routeLocalNameBudget, budgetRouteSchedule,
      scheduleNormalFormReadback, provenancePkg, readbackPkg⟩

theorem MetaCICCriticalPathNormalizationObstructionRouteCoverage [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal normalizationRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont strongNorm normalForm normalizationRead →
        Cont obstruction continuation replayRead →
          PkgSig bundle normalizationRead pkg →
            SemanticNameCert
                (fun row : BHist =>
                  (hsame row normalizationRead ∨ hsame row replayRead) ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row strongNorm ∨ hsame row normalForm ∨ hsame row obstruction ∨
                    hsame row handoff ∨ hsame row continuation ∨ hsame row localName ∨
                      hsame row normalizationRead ∨ hsame row replayRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle normalizationRead pkg ∧ PkgSig bundle realSeal pkg)
                hsame ∧
              UnaryHistory normalizationRead ∧ UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro ledger normalizationRoute replayRoute normalizationPkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, _regseqUnary, _realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨strongNormUnary, normalFormUnary, obstructionUnary, _unblockUnary,
    _dischargeUnary, _handoffUnary, continuationUnary, _provenanceUnary,
    _localNameUnary, _strongNormNormalFormContinuation, _unblockObstructionDischarge,
    _handoffLocalName, provenancePkg⟩ := packet
  have normalizationUnary : UnaryHistory normalizationRead :=
    unary_cont_closed strongNormUnary normalFormUnary normalizationRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed obstructionUnary continuationUnary replayRoute
  have sourceNormalization :
      (fun row : BHist =>
        (hsame row normalizationRead ∨ hsame row replayRead) ∧ UnaryHistory row)
          normalizationRead := by
    exact ⟨Or.inl (hsame_refl normalizationRead), normalizationUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row normalizationRead ∨ hsame row replayRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row strongNorm ∨ hsame row normalForm ∨ hsame row obstruction ∨
              hsame row handoff ∨ hsame row continuation ∨ hsame row localName ∨
                hsame row normalizationRead ∨ hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle normalizationRead pkg ∧ PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro normalizationRead sourceNormalization
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
        constructor
        · cases source.left with
          | inl sameNorm =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameNorm)
          | inr sameReplay =>
              exact Or.inr (hsame_trans (hsame_symm sameRows) sameReplay)
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameNorm =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameNorm))))))
      | inr sameReplay =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sameReplay))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, normalizationPkg, realSealPkg⟩
  }
  exact ⟨cert, normalizationUnary, replayUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
