import BEDC.Derived.WronskianUp.ObligationClosurePackage

namespace BEDC.Derived.WronskianUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem WronskianCarrier_public_determinant_export [AskSetup] [PackageSetup]
    {F D J Omega S R E H C P N determinantRead valueRead sealRead witnessRead
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    WronskianObligationRowSpec F D J Omega S R E H C P N F →
      WronskianObligationRowSpec F D J Omega S R E H C P N D →
        WronskianObligationRowSpec F D J Omega S R E H C P N J →
          WronskianObligationRowSpec F D J Omega S R E H C P N Omega →
            WronskianObligationRowSpec F D J Omega S R E H C P N E →
              UnaryHistory F →
                UnaryHistory D →
                  UnaryHistory J →
                    UnaryHistory Omega →
                      UnaryHistory S →
                        UnaryHistory R →
                          UnaryHistory E →
                            UnaryHistory H →
                              Cont F D J →
                                Cont J Omega determinantRead →
                                  Cont S R valueRead →
                                    Cont valueRead E sealRead →
                                      Cont determinantRead sealRead witnessRead →
                                        Cont sealRead H publicRead →
                                          PkgSig bundle publicRead pkg →
                                            SemanticNameCert
                                                (fun row : BHist =>
                                                  hsame row publicRead ∧ UnaryHistory row)
                                                (fun row : BHist =>
                                                  WronskianObligationRowSpec F D J Omega S R
                                                      E H C P N row ∨
                                                    hsame row determinantRead ∨
                                                      hsame row valueRead ∨
                                                        hsame row sealRead ∨
                                                          hsame row witnessRead ∨
                                                            hsame row publicRead)
                                                (fun row : BHist =>
                                                  UnaryHistory row ∧
                                                    PkgSig bundle publicRead pkg)
                                                hsame ∧
                                              UnaryHistory publicRead ∧
                                                PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame SemanticNameCert
  intro _fSpec _dSpec _jSpec _omegaSpec _eSpec _fUnary _dUnary jUnary omegaUnary sUnary
    rUnary eUnary hUnary _familyRoute determinantRoute valueRoute sealRoute witnessRoute
    publicRoute publicPkg
  have determinantUnary : UnaryHistory determinantRead :=
    unary_cont_closed jUnary omegaUnary determinantRoute
  have valueUnary : UnaryHistory valueRead :=
    unary_cont_closed sUnary rUnary valueRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed valueUnary eUnary sealRoute
  have _witnessUnary : UnaryHistory witnessRead :=
    unary_cont_closed determinantUnary sealUnary witnessRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed sealUnary hUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            WronskianObligationRowSpec F D J Omega S R E H C P N row ∨
              hsame row determinantRead ∨ hsame row valueRead ∨ hsame row sealRead ∨
                hsame row witnessRead ∨ hsame row publicRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
      exact ⟨source.right, publicPkg⟩
  }
  exact ⟨cert, publicUnary, publicPkg⟩

end BEDC.Derived.WronskianUp
