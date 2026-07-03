import BEDC.Derived.WronskianUp.Carrier

namespace BEDC.Derived.WronskianUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem WronskianCarrier_scope_replay_certificate [AskSetup] [PackageSetup]
    {F D J Omega S R E H C P N scopeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    WronskianCarrier F D J Omega S R E H C P N bundle pkg →
      Cont E H scopeRead →
        PkgSig bundle scopeRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row scopeRead ∧ UnaryHistory row)
              (WronskianObligationRowSpec F D J Omega S R E H C P N)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont E H scopeRead ∧ PkgSig bundle P pkg ∧
                  PkgSig bundle scopeRead pkg)
              hsame ∧
            UnaryHistory scopeRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert
  intro carrier scopeRoute scopePkg
  obtain ⟨_fUnary, _dUnary, _jUnary, _omegaUnary, _sUnary, _rUnary, eUnary, hUnary,
    _cUnary, _pUnary, _nUnary, _familyRoute, _determinantRoute, _valueRoute,
    carrierScopeRoute, provenancePkg, _namePkg⟩ := carrier
  have scopeUnary : UnaryHistory scopeRead :=
    unary_cont_closed eUnary hUnary scopeRoute
  have carrierScopeSame : hsame C scopeRead :=
    cont_deterministic carrierScopeRoute scopeRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row scopeRead ∧ UnaryHistory row)
          (WronskianObligationRowSpec F D J Omega S R E H C P N)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont E H scopeRead ∧ PkgSig bundle P pkg ∧
              PkgSig bundle scopeRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro scopeRead ⟨hsame_refl scopeRead, scopeUnary⟩
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
      have rowSameC : hsame _row C :=
        hsame_trans source.left (hsame_symm carrierScopeSame)
      exact
        Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
          Or.inr <| Or.inr <| Or.inl rowSameC
    ledger_sound := by
      intro _row source
      exact ⟨source.right, scopeRoute, provenancePkg, scopePkg⟩
  }
  exact ⟨cert, scopeUnary⟩

end BEDC.Derived.WronskianUp
