import BEDC.Derived.DyadicSupremumUp.NameCertObligations

namespace BEDC.Derived.DyadicSupremumUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicSupremumFiniteWindowExhaustion [AskSetup] [PackageSetup]
    {bounded approximation window tolerance handoff realSeal transport replay provenance name
      lowerRead locatedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    (UnaryHistory bounded ∧ UnaryHistory approximation ∧ UnaryHistory window ∧
        UnaryHistory tolerance ∧ UnaryHistory handoff ∧ UnaryHistory realSeal ∧
          UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
            UnaryHistory name ∧ Cont bounded window tolerance ∧
              Cont approximation tolerance lowerRead ∧ Cont lowerRead handoff locatedRead ∧
                hsame transport name ∧ PkgSig bundle provenance pkg) →
      SemanticNameCert
          (fun row : BHist => hsame row locatedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row bounded ∨ hsame row approximation ∨ hsame row window ∨
              hsame row tolerance ∨ hsame row lowerRead ∨ hsame row handoff ∨
                hsame row locatedRead)
          (fun row : BHist => hsame row locatedRead ∧ PkgSig bundle provenance pkg)
          hsame ∧
        UnaryHistory lowerRead ∧ UnaryHistory locatedRead ∧
          PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle SemanticNameCert hsame UnaryHistory
  intro packet
  obtain ⟨_boundedUnary, approximationUnary, _windowUnary, toleranceUnary, handoffUnary,
    _realSealUnary, _transportUnary, _replayUnary, _provenanceUnary, _nameUnary,
    _boundedWindowTolerance, approximationToleranceLower, lowerHandoffLocated,
    _transportName, provenancePkg⟩ := packet
  have lowerUnary : UnaryHistory lowerRead :=
    unary_cont_closed approximationUnary toleranceUnary approximationToleranceLower
  have locatedUnary : UnaryHistory locatedRead :=
    unary_cont_closed lowerUnary handoffUnary lowerHandoffLocated
  have locatedSource :
      (fun row : BHist => hsame row locatedRead ∧ UnaryHistory row) locatedRead := by
    exact ⟨hsame_refl locatedRead, locatedUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row locatedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row bounded ∨ hsame row approximation ∨ hsame row window ∨
              hsame row tolerance ∨ hsame row lowerRead ∨ hsame row handoff ∨
                hsame row locatedRead)
          (fun row : BHist => hsame row locatedRead ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro locatedRead locatedSource
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, provenancePkg⟩
  }
  exact ⟨cert, lowerUnary, locatedUnary, provenancePkg⟩

end BEDC.Derived.DyadicSupremumUp
