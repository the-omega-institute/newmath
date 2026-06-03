import BEDC.Derived.RepresentedSpaceUp

namespace BEDC.Derived.RepresentedSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RepresentedSpaceCarrier_admissible_finality [AskSetup] [PackageSetup]
    {name schedule relation target transport replay provenance localName scheduledSource
      targetRead cauchyName finalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.RepresentedSpaceUp name schedule relation target transport replay
        provenance localName bundle pkg →
      Cont name schedule scheduledSource →
        Cont relation target targetRead →
          Cont scheduledSource targetRead cauchyName →
            Cont cauchyName provenance finalRead →
              PkgSig bundle finalRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row finalRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row name ∨ hsame row schedule ∨ hsame row relation ∨
                        hsame row target ∨ hsame row cauchyName ∨ hsame row finalRead)
                    (fun row : BHist =>
                      hsame row finalRead ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle finalRead pkg)
                    hsame ∧
                  UnaryHistory scheduledSource ∧ UnaryHistory targetRead ∧
                    UnaryHistory cauchyName ∧ UnaryHistory finalRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier nameScheduleSource relationTargetRead cauchyRoute finalRoute finalPkg
  obtain ⟨nameUnary, scheduleUnary, relationUnary, targetUnary, _transportUnary,
    _replayUnary, provenanceUnary, _localNameUnary, _nameScheduleReplay,
    _relationTargetTransport, _localNameTransport, provenancePkg⟩ := carrier
  have scheduledUnary : UnaryHistory scheduledSource :=
    unary_cont_closed nameUnary scheduleUnary nameScheduleSource
  have targetReadUnary : UnaryHistory targetRead :=
    unary_cont_closed relationUnary targetUnary relationTargetRead
  have cauchyUnary : UnaryHistory cauchyName :=
    unary_cont_closed scheduledUnary targetReadUnary cauchyRoute
  have finalUnary : UnaryHistory finalRead :=
    unary_cont_closed cauchyUnary provenanceUnary finalRoute
  have sourceFinal :
      (fun row : BHist => hsame row finalRead ∧ UnaryHistory row) finalRead := by
    exact ⟨hsame_refl finalRead, finalUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row finalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row name ∨ hsame row schedule ∨ hsame row relation ∨
              hsame row target ∨ hsame row cauchyName ∨ hsame row finalRead)
          (fun row : BHist =>
            hsame row finalRead ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle finalRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro finalRead sourceFinal
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, provenancePkg, finalPkg⟩
  }
  exact ⟨cert, scheduledUnary, targetReadUnary, cauchyUnary, finalUnary⟩

end BEDC.Derived.RepresentedSpaceUp
