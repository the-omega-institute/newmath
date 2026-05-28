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

theorem MetaCICCriticalPathCarrier_substitution_boundary_routing [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName substitutionRead l10Read : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg ->
      Cont handoff obstruction substitutionRead ->
        Cont substitutionRead dischargeSocket l10Read ->
          PkgSig bundle l10Read pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row l10Read ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row handoff ∨ hsame row obstruction ∨ hsame row dischargeSocket ∨
                    hsame row transport ∨ hsame row route ∨ hsame row provenance ∨
                      hsame row localName ∨ hsame row l10Read)
                (fun row : BHist =>
                  PkgSig bundle provenance pkg ∧ PkgSig bundle l10Read pkg ∧
                    hsame row l10Read)
                hsame ∧
              UnaryHistory substitutionRead ∧ UnaryHistory l10Read := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro packet substitutionRoute l10Route l10Pkg
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, handoffUnary,
    dischargeSocketUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _localNameUnary, _strongNormNormalFormRoute, _handoffObstructionSocket,
    _transportLocalName, provenancePkg⟩ := packet
  have substitutionReadUnary : UnaryHistory substitutionRead :=
    unary_cont_closed handoffUnary obstructionUnary substitutionRoute
  have l10ReadUnary : UnaryHistory l10Read :=
    unary_cont_closed substitutionReadUnary dischargeSocketUnary l10Route
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row l10Read ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row handoff ∨ hsame row obstruction ∨ hsame row dischargeSocket ∨
              hsame row transport ∨ hsame row route ∨ hsame row provenance ∨
                hsame row localName ∨ hsame row l10Read)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle l10Read pkg ∧
              hsame row l10Read)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro l10Read ⟨hsame_refl l10Read, l10ReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, l10Pkg, source.left⟩
  }
  exact ⟨cert, substitutionReadUnary, l10ReadUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
