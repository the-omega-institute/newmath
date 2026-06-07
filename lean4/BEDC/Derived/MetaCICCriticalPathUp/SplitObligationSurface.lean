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

theorem MetaCICCriticalPathSplitObligationSurface [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName leftRead rightRead joinedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction unblock discharge handoff
        continuation provenance localName bundle pkg →
      Cont strongNorm normalForm leftRead →
        Cont handoff obstruction rightRead →
          Cont leftRead rightRead joinedRead →
            PkgSig bundle joinedRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row joinedRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row leftRead ∨ hsame row rightRead ∨ hsame row joinedRead ∨
                      hsame row obstruction ∨ hsame row discharge)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont strongNorm normalForm leftRead ∧
                      Cont handoff obstruction rightRead ∧
                        Cont leftRead rightRead joinedRead ∧
                          PkgSig bundle joinedRead pkg ∧ PkgSig bundle provenance pkg)
                  hsame ∧
                UnaryHistory leftRead ∧ UnaryHistory rightRead ∧ UnaryHistory joinedRead ∧
                  PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro packet strongNormNormalFormLeft handoffObstructionRight leftRightJoined joinedPkg
  obtain ⟨strongNormUnary, normalFormUnary, obstructionUnary, _unblockUnary,
    _dischargeUnary, handoffUnary, _continuationUnary, _provenanceUnary, _localNameUnary,
    _strongNormNormalFormContinuation, _handoffObstructionDischarge, _transportLocalName,
    provenancePkg⟩ := packet
  have leftUnary : UnaryHistory leftRead :=
    unary_cont_closed strongNormUnary normalFormUnary strongNormNormalFormLeft
  have rightUnary : UnaryHistory rightRead :=
    unary_cont_closed handoffUnary obstructionUnary handoffObstructionRight
  have joinedUnary : UnaryHistory joinedRead :=
    unary_cont_closed leftUnary rightUnary leftRightJoined
  have joinedSource :
      (fun row : BHist => hsame row joinedRead ∧ UnaryHistory row) joinedRead := by
    exact ⟨hsame_refl joinedRead, joinedUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row joinedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row leftRead ∨ hsame row rightRead ∨ hsame row joinedRead ∨
              hsame row obstruction ∨ hsame row discharge)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont strongNorm normalForm leftRead ∧
              Cont handoff obstruction rightRead ∧ Cont leftRead rightRead joinedRead ∧
                PkgSig bundle joinedRead pkg ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro joinedRead joinedSource
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
      exact Or.inr (Or.inr (Or.inl source.left))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, strongNormNormalFormLeft, handoffObstructionRight, leftRightJoined,
          joinedPkg, provenancePkg⟩
  }
  exact ⟨cert, leftUnary, rightUnary, joinedUnary, provenancePkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
