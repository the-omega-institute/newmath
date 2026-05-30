import BEDC.Derived.RepresentedSpaceUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.RepresentedSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RepresentedSpaceCarrier_realizer_readback_window [AskSetup] [PackageSetup]
    {name schedule relation target transport replay provenance localName scheduleRead targetRead
      readback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.RepresentedSpaceUp name schedule relation target transport replay
        provenance localName bundle pkg →
      Cont name schedule scheduleRead →
        Cont target localName targetRead →
          Cont scheduleRead targetRead readback →
            PkgSig bundle scheduleRead pkg →
              PkgSig bundle targetRead pkg →
                PkgSig bundle readback pkg →
                  SemanticNameCert
                      (fun row : BHist =>
                        (hsame row scheduleRead ∨ hsame row targetRead ∨
                          hsame row readback) ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row name ∨ hsame row schedule ∨ hsame row relation ∨
                          hsame row target ∨ hsame row scheduleRead ∨
                            hsame row targetRead ∨ hsame row readback)
                      (fun row : BHist =>
                        (hsame row scheduleRead ∨ hsame row targetRead ∨
                          hsame row readback) ∧ PkgSig bundle provenance pkg)
                      hsame ∧
                    UnaryHistory scheduleRead ∧ UnaryHistory targetRead ∧
                      UnaryHistory readback := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier nameScheduleRead targetLocalNameRead scheduleTargetRead _scheduleReadPkg
    _targetReadPkg _readbackPkg
  obtain ⟨nameUnary, scheduleUnary, _relationUnary, targetUnary, _transportUnary,
    _replayUnary, _provenanceUnary, localNameUnary, _nameScheduleReplay,
    _relationTargetTransport, _localNameTransport, provenancePkg⟩ := carrier
  have scheduleReadUnary : UnaryHistory scheduleRead :=
    unary_cont_closed nameUnary scheduleUnary nameScheduleRead
  have targetReadUnary : UnaryHistory targetRead :=
    unary_cont_closed targetUnary localNameUnary targetLocalNameRead
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed scheduleReadUnary targetReadUnary scheduleTargetRead
  have sourceScheduleRead :
      (fun row : BHist =>
        (hsame row scheduleRead ∨ hsame row targetRead ∨ hsame row readback) ∧
          UnaryHistory row) scheduleRead := by
    exact ⟨Or.inl (hsame_refl scheduleRead), scheduleReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row scheduleRead ∨ hsame row targetRead ∨ hsame row readback) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row name ∨ hsame row schedule ∨ hsame row relation ∨
              hsame row target ∨ hsame row scheduleRead ∨ hsame row targetRead ∨
                hsame row readback)
          (fun row : BHist =>
            (hsame row scheduleRead ∨ hsame row targetRead ∨ hsame row readback) ∧
              PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro scheduleRead sourceScheduleRead
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
        cases source.left with
        | inl sameSchedule =>
            exact
              ⟨Or.inl (hsame_trans (hsame_symm sameRows) sameSchedule),
                unary_transport source.right sameRows⟩
        | inr rest =>
            cases rest with
            | inl sameTarget =>
                exact
                  ⟨Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameTarget)),
                    unary_transport source.right sameRows⟩
            | inr sameReadback =>
                exact
                  ⟨Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameReadback)),
                    unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameSchedule =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameSchedule))))
      | inr rest =>
          cases rest with
          | inl sameTarget =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameTarget)))))
          | inr sameReadback =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sameReadback)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, provenancePkg⟩
  }
  exact ⟨cert, scheduleReadUnary, targetReadUnary, readbackUnary⟩

end BEDC.Derived.RepresentedSpaceUp
