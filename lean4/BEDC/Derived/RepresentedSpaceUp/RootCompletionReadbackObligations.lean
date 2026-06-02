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

theorem RepresentedSpaceCarrier_root_completion_readback_obligations [AskSetup] [PackageSetup]
    {name schedule relation target transport replay provenance localName scheduledSource
      targetRead completionRead directRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.RepresentedSpaceUp name schedule relation target transport replay provenance
        localName bundle pkg ->
      Cont name schedule scheduledSource ->
        Cont relation target targetRead ->
          Cont scheduledSource targetRead completionRead ->
            Cont name target directRead ->
              hsame completionRead directRead ->
                PkgSig bundle completionRead pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row name ∨ hsame row schedule ∨ hsame row relation ∨
                          hsame row target ∨ hsame row completionRead)
                      (fun row : BHist =>
                        hsame row completionRead ∧ PkgSig bundle provenance pkg ∧
                          PkgSig bundle completionRead pkg)
                      hsame ∧
                    UnaryHistory scheduledSource ∧ UnaryHistory targetRead ∧
                      UnaryHistory completionRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier nameScheduleRead relationTargetRead scheduleTargetCompletion
    _nameTargetDirect completionDirectSame completionPkg
  obtain ⟨nameUnary, scheduleUnary, relationUnary, targetUnary, _transportUnary,
    _replayUnary, _provenanceUnary, _localNameUnary, _nameScheduleReplay,
    _relationTargetTransport, _localNameTransport, provenancePkg⟩ := carrier
  have scheduledUnary : UnaryHistory scheduledSource :=
    unary_cont_closed nameUnary scheduleUnary nameScheduleRead
  have targetReadUnary : UnaryHistory targetRead :=
    unary_cont_closed relationUnary targetUnary relationTargetRead
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed scheduledUnary targetReadUnary scheduleTargetCompletion
  have directReadUnary : UnaryHistory directRead :=
    unary_transport completionUnary completionDirectSame
  have sourceCompletion :
      (fun row : BHist => hsame row completionRead ∧ UnaryHistory row) completionRead := by
    exact ⟨hsame_refl completionRead, completionUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row name ∨ hsame row schedule ∨ hsame row relation ∨ hsame row target ∨
              hsame row completionRead)
          (fun row : BHist =>
            hsame row completionRead ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle completionRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro completionRead sourceCompletion
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
      exact ⟨source.left, provenancePkg, completionPkg⟩
  }
  exact ⟨cert, scheduledUnary, targetReadUnary, completionUnary⟩

end BEDC.Derived.RepresentedSpaceUp
