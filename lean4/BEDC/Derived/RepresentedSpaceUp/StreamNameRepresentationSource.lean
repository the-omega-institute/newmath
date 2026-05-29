import BEDC.Derived.RepresentedSpaceUp.AdmissibleNameCoverage
import BEDC.Derived.RepresentedSpaceUp.RealizationTransport
import BEDC.FKernel.NameCert

namespace BEDC.Derived.RepresentedSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RepresentedSpaceCarrier_streamname_representation_source [AskSetup] [PackageSetup]
    {name schedule relation target transport replay provenance localName scheduledSource
      targetRead sourceTargetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.RepresentedSpaceUp name schedule relation target transport replay
        provenance localName bundle pkg ->
      Cont name schedule scheduledSource ->
        Cont relation target targetRead ->
          Cont scheduledSource targetRead sourceTargetRead ->
            PkgSig bundle sourceTargetRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row sourceTargetRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row name ∨ hsame row schedule ∨ hsame row relation ∨
                      hsame row target ∨ hsame row sourceTargetRead)
                  (fun row : BHist =>
                    hsame row sourceTargetRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle sourceTargetRead pkg)
                  hsame ∧
                UnaryHistory scheduledSource ∧ UnaryHistory targetRead ∧
                  UnaryHistory sourceTargetRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier scheduledRoute targetRoute sourceTargetRoute sourceTargetPkg
  obtain ⟨nameUnary, scheduleUnary, relationUnary, targetUnary, _transportUnary,
    _replayUnary, _provenanceUnary, _localNameUnary, _nameScheduleReplay,
    _relationTargetTransport, _localNameTransport, provenancePkg⟩ := carrier
  have scheduledUnary : UnaryHistory scheduledSource :=
    unary_cont_closed nameUnary scheduleUnary scheduledRoute
  have targetReadUnary : UnaryHistory targetRead :=
    unary_cont_closed relationUnary targetUnary targetRoute
  have sourceTargetUnary : UnaryHistory sourceTargetRead :=
    unary_cont_closed scheduledUnary targetReadUnary sourceTargetRoute
  have sourceTargetSource :
      (fun row : BHist => hsame row sourceTargetRead ∧ UnaryHistory row)
        sourceTargetRead := by
    exact ⟨hsame_refl sourceTargetRead, sourceTargetUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sourceTargetRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row name ∨ hsame row schedule ∨ hsame row relation ∨
              hsame row target ∨ hsame row sourceTargetRead)
          (fun row : BHist =>
            hsame row sourceTargetRead ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle sourceTargetRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sourceTargetRead sourceTargetSource
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
      exact ⟨source.left, provenancePkg, sourceTargetPkg⟩
  }
  exact ⟨cert, scheduledUnary, targetReadUnary, sourceTargetUnary⟩

end BEDC.Derived.RepresentedSpaceUp
