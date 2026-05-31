import BEDC.Derived.MetaCICConfluenceAuditPacketUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.MetaCICConfluenceAuditPacketUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICConfluenceAuditPacketClosedSubstitutionBoundary [AskSetup] [PackageSetup]
    {_diamond _closedStar _normal _atomFragments substitutionBoundary closedA closedB obstruction
      replay provenance localName finalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory substitutionBoundary →
      UnaryHistory closedA →
        UnaryHistory closedB →
          UnaryHistory obstruction →
            UnaryHistory replay →
              Cont substitutionBoundary closedA replay →
                Cont replay closedB finalRead →
                  PkgSig bundle provenance pkg →
                    PkgSig bundle localName pkg →
                      SemanticNameCert
                          (fun row : BHist => hsame row finalRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row substitutionBoundary ∨ hsame row closedA ∨
                              hsame row closedB ∨ hsame row obstruction ∨
                                hsame row finalRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                              PkgSig bundle localName pkg)
                          hsame ∧
                        UnaryHistory finalRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame UnaryHistory
  intro substitutionBoundaryUnary closedAUnary closedBUnary _obstructionUnary _replayUnary
    replayRoute finalReadRoute provenancePkg localNamePkg
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed substitutionBoundaryUnary closedAUnary replayRoute
  have finalReadUnary : UnaryHistory finalRead :=
    unary_cont_closed replayUnary closedBUnary finalReadRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row finalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row substitutionBoundary ∨ hsame row closedA ∨ hsame row closedB ∨
              hsame row obstruction ∨ hsame row finalRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro finalRead ⟨hsame_refl finalRead, finalReadUnary⟩
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
      intro _row source
      exact ⟨source.right, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, finalReadUnary⟩

end BEDC.Derived.MetaCICConfluenceAuditPacketUp
