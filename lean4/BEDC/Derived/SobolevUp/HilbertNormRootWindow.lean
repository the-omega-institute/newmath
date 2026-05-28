import BEDC.Derived.SobolevUp

namespace BEDC.Derived.SobolevUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SobolevCarrier_hilbert_norm_root_window [AskSetup] [PackageSetup]
    {domain base codomain magnitude gradient transports routes provenance localCert normRead
      rootWindow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SobolevCarrier domain base codomain magnitude gradient transports routes provenance
        localCert bundle pkg ->
      Cont codomain magnitude normRead ->
        Cont normRead gradient rootWindow ->
          PkgSig bundle rootWindow pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row rootWindow ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row codomain ∨ hsame row magnitude ∨ hsame row gradient ∨
                    hsame row rootWindow)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle rootWindow pkg ∧
                    PkgSig bundle provenance pkg)
                hsame ∧
              UnaryHistory rootWindow ∧ Cont codomain magnitude normRead ∧
                Cont normRead gradient rootWindow ∧ Cont domain base codomain ∧
                  Cont codomain magnitude gradient ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: SobolevCarrier BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier codomainMagnitudeNorm normGradientRoot rootPkg
  obtain ⟨_domainUnary, _baseUnary, codomainUnary, magnitudeUnary, gradientUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _localCertUnary, domainBaseCodomain,
    codomainMagnitudeGradient, _gradientTransportsRoutes, _routesProvenanceLocalCert,
    provenancePkg⟩ := carrier
  have normUnary : UnaryHistory normRead :=
    unary_cont_closed codomainUnary magnitudeUnary codomainMagnitudeNorm
  have rootUnary : UnaryHistory rootWindow :=
    unary_cont_closed normUnary gradientUnary normGradientRoot
  have sourceRoot :
      (fun row : BHist => hsame row rootWindow ∧ UnaryHistory row) rootWindow := by
    exact ⟨hsame_refl rootWindow, rootUnary⟩
  have core :
      NameCert (fun row : BHist => hsame row rootWindow ∧ UnaryHistory row) hsame := by
    exact {
      carrier_inhabited := Exists.intro rootWindow sourceRoot
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _left _middle _right sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row other sameRows sourceRow
        have sameOtherRoot : hsame other rootWindow :=
          hsame_trans (hsame_symm sameRows) sourceRow.left
        have otherUnary : UnaryHistory other :=
          unary_transport sourceRow.right sameRows
        exact ⟨sameOtherRoot, otherUnary⟩
    }
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row rootWindow ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row codomain ∨ hsame row magnitude ∨ hsame row gradient ∨
              hsame row rootWindow)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle rootWindow pkg ∧ PkgSig bundle provenance pkg)
          hsame := by
    exact {
      core := core
      pattern_sound := by
        intro _row sourceRow
        exact Or.inr (Or.inr (Or.inr sourceRow.left))
      ledger_sound := by
        intro _row sourceRow
        exact ⟨sourceRow.right, rootPkg, provenancePkg⟩
    }
  exact
    ⟨cert, rootUnary, codomainMagnitudeNorm, normGradientRoot, domainBaseCodomain,
      codomainMagnitudeGradient, provenancePkg⟩

end BEDC.Derived.SobolevUp
