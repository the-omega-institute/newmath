import BEDC.Derived.WronskianUp.L10ScopeBinding

namespace BEDC.Derived.WronskianUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem WronskianCarrier_certificate_rows [AskSetup] [PackageSetup]
    {F D J Omega S R E H C P N : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    WronskianCarrier F D J Omega S R E H C P N bundle pkg →
      WronskianObligationRowSpec F D J Omega S R E H C P N F ∧
        WronskianObligationRowSpec F D J Omega S R E H C P N D ∧
          WronskianObligationRowSpec F D J Omega S R E H C P N J ∧
            WronskianObligationRowSpec F D J Omega S R E H C P N Omega ∧
              WronskianObligationRowSpec F D J Omega S R E H C P N S ∧
                WronskianObligationRowSpec F D J Omega S R E H C P N R ∧
                  WronskianObligationRowSpec F D J Omega S R E H C P N E ∧
                    WronskianObligationRowSpec F D J Omega S R E H C P N H ∧
                      WronskianObligationRowSpec F D J Omega S R E H C P N C ∧
                        WronskianObligationRowSpec F D J Omega S R E H C P N P ∧
                          WronskianObligationRowSpec F D J Omega S R E H C P N N ∧
                            UnaryHistory Omega ∧ Cont F D J ∧ Cont J Omega E ∧
                              Cont S R E ∧ Cont E H C ∧ PkgSig bundle P pkg ∧
                                PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame UnaryHistory
  intro carrier
  obtain ⟨_fUnary, _dUnary, _jUnary, omegaUnary, _sUnary, _rUnary, _eUnary,
    _hUnary, _cUnary, _pUnary, _nUnary, familyRoute, determinantRoute, valueRoute,
    scopeRoute, provenancePkg, namePkg⟩ := carrier
  have fRow : WronskianObligationRowSpec F D J Omega S R E H C P N F :=
    Or.inl (hsame_refl F)
  have dRow : WronskianObligationRowSpec F D J Omega S R E H C P N D :=
    Or.inr (Or.inl (hsame_refl D))
  have jRow : WronskianObligationRowSpec F D J Omega S R E H C P N J :=
    Or.inr (Or.inr (Or.inl (hsame_refl J)))
  have omegaRow : WronskianObligationRowSpec F D J Omega S R E H C P N Omega :=
    Or.inr (Or.inr (Or.inr (Or.inl (hsame_refl Omega))))
  have sRow : WronskianObligationRowSpec F D J Omega S R E H C P N S :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hsame_refl S)))))
  have rRow : WronskianObligationRowSpec F D J Omega S R E H C P N R :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hsame_refl R))))))
  have eRow : WronskianObligationRowSpec F D J Omega S R E H C P N E := by
    repeat (first | exact Or.inl (hsame_refl E) | apply Or.inr)
  have hRow : WronskianObligationRowSpec F D J Omega S R E H C P N H := by
    repeat (first | exact Or.inl (hsame_refl H) | apply Or.inr)
  have cRow : WronskianObligationRowSpec F D J Omega S R E H C P N C := by
    repeat (first | exact Or.inl (hsame_refl C) | apply Or.inr)
  have pRow : WronskianObligationRowSpec F D J Omega S R E H C P N P := by
    repeat (first | exact Or.inl (hsame_refl P) | apply Or.inr)
  have nRow : WronskianObligationRowSpec F D J Omega S R E H C P N N := by
    repeat (first | exact hsame_refl N | exact Or.inl (hsame_refl N) | apply Or.inr)
  exact
    ⟨fRow, dRow, jRow, omegaRow, sRow, rRow, eRow, hRow, cRow, pRow, nRow,
      omegaUnary, familyRoute, determinantRoute, valueRoute, scopeRoute, provenancePkg,
      namePkg⟩

end BEDC.Derived.WronskianUp
