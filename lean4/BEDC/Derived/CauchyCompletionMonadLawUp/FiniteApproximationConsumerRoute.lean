import BEDC.Derived.CauchyCompletionMonadLawUp.NameCertObligations

namespace BEDC.Derived.CauchyCompletionMonadLawUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCompletionMonadLawFiniteApproximationConsumerRoute [AskSetup] [PackageSetup]
    {M U I B S D R H C P N unitRead bindRead regularRead approximationRead
      totalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionMonadLawCarrier M U I B S D R H C P N bundle pkg ->
      Cont M U unitRead ->
        Cont I B bindRead ->
          Cont S D regularRead ->
            Cont regularRead R approximationRead ->
              Cont approximationRead N totalRead ->
                PkgSig bundle regularRead pkg ->
                  PkgSig bundle totalRead pkg ->
                    SemanticNameCert
                        (fun row : BHist => hsame row totalRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row M ∨ hsame row U ∨ hsame row I ∨ hsame row B ∨
                            hsame row S ∨ hsame row D ∨ hsame row R ∨
                              hsame row regularRead ∨ hsame row approximationRead ∨
                                hsame row totalRead)
                        (fun row : BHist =>
                          hsame row totalRead ∧ PkgSig bundle totalRead pkg)
                        hsame ∧
                      UnaryHistory unitRead ∧ UnaryHistory bindRead ∧
                        UnaryHistory regularRead ∧ UnaryHistory approximationRead ∧
                          UnaryHistory totalRead ∧ Cont regularRead R approximationRead ∧
                            Cont approximationRead N totalRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier unitRoute bindRoute regularRoute approximationRoute totalRoute
    _regularPkg totalPkg
  obtain ⟨mUnary, uUnary, iUnary, bUnary, sUnary, dUnary, rUnary, _hUnary, _cUnary,
    _pUnary, nUnary, _sameHC, _provenancePkg, _namePkg⟩ := carrier
  have unitUnary : UnaryHistory unitRead :=
    unary_cont_closed mUnary uUnary unitRoute
  have bindUnary : UnaryHistory bindRead :=
    unary_cont_closed iUnary bUnary bindRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed sUnary dUnary regularRoute
  have approximationUnary : UnaryHistory approximationRead :=
    unary_cont_closed regularUnary rUnary approximationRoute
  have totalUnary : UnaryHistory totalRead :=
    unary_cont_closed approximationUnary nUnary totalRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row totalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row U ∨ hsame row I ∨ hsame row B ∨ hsame row S ∨
              hsame row D ∨ hsame row R ∨ hsame row regularRead ∨
                hsame row approximationRead ∨ hsame row totalRead)
          (fun row : BHist => hsame row totalRead ∧ PkgSig bundle totalRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro totalRead ⟨hsame_refl totalRead, totalUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, totalPkg⟩
  }
  exact
    ⟨cert, unitUnary, bindUnary, regularUnary, approximationUnary, totalUnary,
      approximationRoute, totalRoute⟩

end BEDC.Derived.CauchyCompletionMonadLawUp
