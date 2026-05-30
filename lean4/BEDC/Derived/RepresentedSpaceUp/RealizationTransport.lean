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

theorem RepresentedSpaceCarrier_realization_transport [AskSetup] [PackageSetup]
    {name schedule relation target transport replay provenance localName realizedRead
      transportedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.RepresentedSpaceUp name schedule relation target transport replay provenance
        localName bundle pkg ->
      Cont relation target realizedRead ->
        Cont realizedRead transport transportedRead ->
          PkgSig bundle transportedRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row transportedRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row name ∨ hsame row schedule ∨ hsame row relation ∨
                    hsame row target ∨ hsame row transport ∨ hsame row transportedRead)
                (fun row : BHist =>
                  hsame row transportedRead ∧ PkgSig bundle transportedRead pkg ∧
                    PkgSig bundle provenance pkg)
                hsame ∧
              UnaryHistory realizedRead ∧ UnaryHistory transportedRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier realizationRoute transportRoute transportedPkg
  obtain ⟨_nameUnary, _scheduleUnary, relationUnary, targetUnary, transportUnary,
    _replayUnary, provenanceUnary, _localNameUnary, _nameScheduleReplay,
    _relationTargetTransport, _localNameTransport, provenancePkg⟩ := carrier
  have realizedUnary : UnaryHistory realizedRead :=
    unary_cont_closed relationUnary targetUnary realizationRoute
  have transportedUnary : UnaryHistory transportedRead :=
    unary_cont_closed realizedUnary transportUnary transportRoute
  have sourceTransported :
      (fun row : BHist => hsame row transportedRead ∧ UnaryHistory row)
        transportedRead := by
    exact ⟨hsame_refl transportedRead, transportedUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row transportedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row name ∨ hsame row schedule ∨ hsame row relation ∨
              hsame row target ∨ hsame row transport ∨ hsame row transportedRead)
          (fun row : BHist =>
            hsame row transportedRead ∧ PkgSig bundle transportedRead pkg ∧
              PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro transportedRead sourceTransported
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
      exact ⟨source.left, transportedPkg, provenancePkg⟩
  }
  exact ⟨cert, realizedUnary, transportedUnary⟩

end BEDC.Derived.RepresentedSpaceUp
