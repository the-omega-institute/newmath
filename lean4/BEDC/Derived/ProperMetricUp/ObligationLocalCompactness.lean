import BEDC.Derived.ProperMetricUp

namespace BEDC.Derived.ProperMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ProperMetricCarrier_obligation_local_compactness [AskSetup] [PackageSetup]
    {X B K L T H C Q N closedCompact locatedRead completeRead localCompactRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ProperMetricCarrier X B K L T H C Q N bundle pkg ->
      Cont B K closedCompact ->
        Cont K L locatedRead ->
          Cont L T completeRead ->
            Cont locatedRead completeRead localCompactRead ->
              PkgSig bundle localCompactRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row localCompactRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row B ∨ hsame row K ∨ hsame row L ∨ hsame row T ∨
                        hsame row closedCompact ∨ hsame row locatedRead ∨
                          hsame row completeRead ∨ hsame row localCompactRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ PkgSig bundle Q pkg ∧
                        PkgSig bundle localCompactRead pkg)
                    hsame ∧
                  UnaryHistory localCompactRead := by
  -- BEDC touchpoint anchor: ProperMetricCarrier BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier closedRoute locatedRoute completeRoute localRoute localPkg
  obtain ⟨_xUnary, bUnary, kUnary, lUnary, tUnary, _hUnary, _cUnary, _qUnary,
    _nUnary, _metricClosedRoute, _compactLocatedRoute, _handoffRoute, properPkg⟩ :=
    carrier
  have closedUnary : UnaryHistory closedCompact :=
    unary_cont_closed bUnary kUnary closedRoute
  have locatedUnary : UnaryHistory locatedRead :=
    unary_cont_closed kUnary lUnary locatedRoute
  have completeUnary : UnaryHistory completeRead :=
    unary_cont_closed lUnary tUnary completeRoute
  have localUnary : UnaryHistory localCompactRead :=
    unary_cont_closed locatedUnary completeUnary localRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row localCompactRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row B ∨ hsame row K ∨ hsame row L ∨ hsame row T ∨
              hsame row closedCompact ∨ hsame row locatedRead ∨
                hsame row completeRead ∨ hsame row localCompactRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle Q pkg ∧ PkgSig bundle localCompactRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro localCompactRead
        ⟨hsame_refl localCompactRead, localUnary⟩
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
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, properPkg, localPkg⟩
  }
  exact ⟨cert, localUnary⟩

end BEDC.Derived.ProperMetricUp
