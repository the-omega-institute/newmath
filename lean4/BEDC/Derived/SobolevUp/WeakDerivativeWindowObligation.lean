import BEDC.Derived.SobolevUp

namespace BEDC.Derived.SobolevUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SobolevCarrier_weak_derivative_window_obligation [AskSetup] [PackageSetup]
    {domain base codomain magnitude gradient transports routes provenance localCert
      derivativeWindow routedWindow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SobolevCarrier domain base codomain magnitude gradient transports routes provenance
        localCert bundle pkg ->
      Cont domain magnitude derivativeWindow ->
        Cont derivativeWindow gradient routedWindow ->
          PkgSig bundle localCert pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row routedWindow ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row domain ∨ hsame row magnitude ∨ hsame row gradient ∨
                    hsame row derivativeWindow ∨ hsame row routedWindow)
                (fun row : BHist =>
                  hsame row routedWindow ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle localCert pkg)
                hsame ∧
              UnaryHistory derivativeWindow ∧ UnaryHistory routedWindow := by
  -- BEDC touchpoint anchor: SobolevCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier domainMagnitudeWindow windowGradientRoute localCertPkg
  obtain ⟨domainUnary, _baseUnary, _codomainUnary, magnitudeUnary, gradientUnary,
    _transportsUnary, _routesUnary, provenanceUnary, _localCertUnary,
    _domainBaseCodomain, _codomainMagnitudeGradient, _gradientTransportsRoutes,
    _routesProvenanceLocalCert, provenancePkg⟩ := carrier
  have derivativeWindowUnary : UnaryHistory derivativeWindow :=
    unary_cont_closed domainUnary magnitudeUnary domainMagnitudeWindow
  have routedWindowUnary : UnaryHistory routedWindow :=
    unary_cont_closed derivativeWindowUnary gradientUnary windowGradientRoute
  have sourceRouted :
      (fun row : BHist => hsame row routedWindow ∧ UnaryHistory row) routedWindow := by
    exact ⟨hsame_refl routedWindow, routedWindowUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row routedWindow ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row domain ∨ hsame row magnitude ∨ hsame row gradient ∨
              hsame row derivativeWindow ∨ hsame row routedWindow)
          (fun row : BHist =>
            hsame row routedWindow ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle localCert pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro routedWindow sourceRouted
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
        cases sameRows
        exact source
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, provenancePkg, localCertPkg⟩
  }
  exact ⟨cert, derivativeWindowUnary, routedWindowUnary⟩

end BEDC.Derived.SobolevUp
