import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.EpigraphUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def EpigraphCarrier [AskSetup] [PackageSetup]
    (D V L O H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory D ∧
    UnaryHistory V ∧
      UnaryHistory L ∧
        UnaryHistory O ∧
          UnaryHistory H ∧
            UnaryHistory C ∧
              UnaryHistory P ∧
                UnaryHistory N ∧
                  Cont D V L ∧
                    Cont L O H ∧
                      PkgSig bundle P pkg ∧
                        PkgSig bundle N pkg

theorem EpigraphNamecertObligations [AskSetup] [PackageSetup]
    {D V L O H C P N queryRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EpigraphCarrier D V L O H C P N bundle pkg ->
      Cont D V L ->
        Cont L O queryRead ->
          Cont queryRead H replayRead ->
            PkgSig bundle P pkg ->
              PkgSig bundle N pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row queryRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row D ∨ hsame row V ∨ hsame row L ∨ hsame row O ∨
                        hsame row H ∨ hsame row queryRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont L O queryRead ∧ PkgSig bundle P pkg ∧
                        PkgSig bundle N pkg)
                    hsame ∧
                  UnaryHistory queryRead ∧ UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier _domainValueRoute queryRoute replayRoute provenancePkg localNamePkg
  obtain ⟨domainUnary, valueUnary, lowerUnary, comparisonUnary, transportUnary,
    _replayUnary, _provenanceUnary, _localNameUnary, _carrierDomainValueRoute,
      _carrierComparisonRoute, _carrierProvenancePkg, _carrierLocalNamePkg⟩ := carrier
  have queryUnary : UnaryHistory queryRead :=
    unary_cont_closed lowerUnary comparisonUnary queryRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed queryUnary transportUnary replayRoute
  have sourceQuery :
      (fun row : BHist => hsame row queryRead ∧ UnaryHistory row) queryRead := by
    exact ⟨hsame_refl queryRead, queryUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row queryRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row V ∨ hsame row L ∨ hsame row O ∨
              hsame row H ∨ hsame row queryRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont L O queryRead ∧ PkgSig bundle P pkg ∧
              PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro queryRead sourceQuery
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
        exact ⟨hsame_trans (hsame_symm sameRows) source.left,
          unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, queryRoute, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, queryUnary, replayUnary⟩

end BEDC.Derived.EpigraphUp
