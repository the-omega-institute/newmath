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

theorem RepresentedSpaceCarrier_realization_exactness [AskSetup] [PackageSetup]
    {name schedule relation target transport replay provenance localName scheduledSource
      realizedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.RepresentedSpaceUp name schedule relation target transport replay provenance
        localName bundle pkg ->
      Cont name schedule scheduledSource ->
        Cont relation target realizedRead ->
          PkgSig bundle realizedRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row realizedRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row name ∨ hsame row schedule ∨ hsame row relation ∨
                    hsame row target ∨ hsame row realizedRead)
                (fun row : BHist =>
                  hsame row realizedRead ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle realizedRead pkg)
                hsame ∧
              UnaryHistory scheduledSource ∧ UnaryHistory realizedRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier scheduleRoute realizationRoute realizedPkg
  obtain ⟨nameUnary, scheduleUnary, relationUnary, targetUnary, _transportUnary,
    _replayUnary, _provenanceUnary, _localNameUnary, _nameScheduleReplay,
    _relationTargetTransport, _localNameTransport, provenancePkg⟩ := carrier
  have scheduledUnary : UnaryHistory scheduledSource :=
    unary_cont_closed nameUnary scheduleUnary scheduleRoute
  have realizedUnary : UnaryHistory realizedRead :=
    unary_cont_closed relationUnary targetUnary realizationRoute
  have sourceRealized :
      (fun row : BHist => hsame row realizedRead ∧ UnaryHistory row) realizedRead := by
    exact ⟨hsame_refl realizedRead, realizedUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realizedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row name ∨ hsame row schedule ∨ hsame row relation ∨
              hsame row target ∨ hsame row realizedRead)
          (fun row : BHist =>
            hsame row realizedRead ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle realizedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realizedRead sourceRealized
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
      exact ⟨source.left, provenancePkg, realizedPkg⟩
  }
  exact ⟨cert, scheduledUnary, realizedUnary⟩

end BEDC.Derived.RepresentedSpaceUp
