import BEDC.Derived.WronskianUp.Carrier

namespace BEDC.Derived.WronskianUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem WronskianCarrier_regular_cauchy_determinant_handoff [AskSetup] [PackageSetup]
    {F D J Omega S R E H C P N determinantRead valueRead sealRead handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    WronskianCarrier F D J Omega S R E H C P N bundle pkg →
      Cont J Omega determinantRead →
        Cont S R valueRead →
          Cont valueRead E sealRead →
            Cont sealRead H handoffRead →
              PkgSig bundle handoffRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row F ∨ hsame row D ∨ hsame row J ∨ hsame row Omega ∨
                        hsame row S ∨ hsame row R ∨ hsame row E ∨ hsame row H ∨
                          hsame row C ∨ hsame row P ∨ hsame row N ∨
                            hsame row determinantRead ∨ hsame row valueRead ∨
                              hsame row sealRead ∨ hsame row handoffRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont J Omega determinantRead ∧
                        Cont S R valueRead ∧ Cont valueRead E sealRead ∧
                          Cont sealRead H handoffRead ∧ PkgSig bundle handoffRead pkg)
                    hsame ∧ UnaryHistory determinantRead ∧ UnaryHistory valueRead ∧
                  UnaryHistory sealRead ∧ UnaryHistory handoffRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier determinantRoute valueRoute sealRoute handoffRoute handoffPkg
  obtain ⟨_fUnary, _dUnary, jUnary, omegaUnary, sUnary, rUnary, eUnary, hUnary,
    _cUnary, _pUnary, _nUnary, _familyRoute, _carrierDeterminantRoute,
    _carrierValueRoute, _scopeRoute, _provenancePkg, _namePkg⟩ := carrier
  have determinantUnary : UnaryHistory determinantRead :=
    unary_cont_closed jUnary omegaUnary determinantRoute
  have valueUnary : UnaryHistory valueRead :=
    unary_cont_closed sUnary rUnary valueRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed valueUnary eUnary sealRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed sealUnary hUnary handoffRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row F ∨ hsame row D ∨ hsame row J ∨ hsame row Omega ∨
              hsame row S ∨ hsame row R ∨ hsame row E ∨ hsame row H ∨
                hsame row C ∨ hsame row P ∨ hsame row N ∨
                  hsame row determinantRead ∨ hsame row valueRead ∨ hsame row sealRead ∨
                    hsame row handoffRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont J Omega determinantRead ∧ Cont S R valueRead ∧
              Cont valueRead E sealRead ∧ Cont sealRead H handoffRead ∧
                PkgSig bundle handoffRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro handoffRead
        ⟨hsame_refl handoffRead, handoffUnary⟩
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
      repeat (first | exact source.left | apply Or.inr)
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, determinantRoute, valueRoute, sealRoute, handoffRoute,
          handoffPkg⟩
  }
  exact ⟨cert, determinantUnary, valueUnary, sealUnary, handoffUnary⟩

end BEDC.Derived.WronskianUp
