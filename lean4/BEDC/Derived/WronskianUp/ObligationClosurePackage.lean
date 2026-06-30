import BEDC.Derived.WronskianUp.ObligationClosureScope
import BEDC.Derived.WronskianUp.SturmSeparationHandoff

namespace BEDC.Derived.WronskianUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem WronskianCarrier_obligation_closure_package [AskSetup] [PackageSetup]
    {F D J Omega S R E H C P N determinantRead valueRead sealRead witnessRead
      sturmRead rootRead handoffRead publicRead : BHist}
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
                              UnaryHistory C →
                                UnaryHistory P →
                                  UnaryHistory N →
                                    Cont F D J →
                                      Cont J Omega determinantRead →
                                        Cont S R valueRead →
                                          Cont valueRead E sealRead →
                                            Cont determinantRead sealRead witnessRead →
                                              Cont Omega S sturmRead →
                                                Cont sturmRead R rootRead →
                                                  Cont rootRead E sealRead →
                                                    Cont sealRead H handoffRead →
                                                      Cont sealRead H publicRead →
                                                        PkgSig bundle witnessRead pkg →
                                                          PkgSig bundle handoffRead pkg →
                                                            PkgSig bundle publicRead pkg →
                                                              SemanticNameCert
                                                                  (fun row : BHist =>
                                                                    hsame row publicRead ∧
                                                                      UnaryHistory row)
                                                                  (fun row : BHist =>
                                                                    WronskianObligationRowSpec F D
                                                                        J Omega S R E H C P N row ∨
                                                                      hsame row determinantRead ∨
                                                                        hsame row valueRead ∨
                                                                          hsame row sealRead ∨
                                                                            hsame row witnessRead ∨
                                                                              hsame row sturmRead ∨
                                                                                hsame row rootRead ∨
                                                                                  hsame row
                                                                                    handoffRead ∨
                                                                                    hsame row
                                                                                      publicRead)
                                                                  (fun row : BHist =>
                                                                    UnaryHistory row ∧
                                                                      PkgSig bundle publicRead pkg)
                                                                  hsame ∧
                                                                UnaryHistory witnessRead ∧
                                                                  UnaryHistory handoffRead ∧
                                                                    UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert UnaryHistory
  intro _fSpec _dSpec _jSpec _omegaSpec _eSpec fUnary dUnary jUnary omegaUnary sUnary
    rUnary eUnary hUnary _cUnary _pUnary _nUnary familyRoute determinantRoute valueRoute
    sealRoute witnessRoute sturmRoute rootRoute rootSealRoute handoffRoute publicRoute
    _witnessPkg _handoffPkg publicPkg
  have valueUnary : UnaryHistory valueRead :=
    unary_cont_closed sUnary rUnary valueRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed valueUnary eUnary sealRoute
  have determinantUnary : UnaryHistory determinantRead :=
    unary_cont_closed jUnary omegaUnary determinantRoute
  have witnessUnary : UnaryHistory witnessRead :=
    unary_cont_closed determinantUnary sealUnary witnessRoute
  have sturmUnary : UnaryHistory sturmRead :=
    unary_cont_closed omegaUnary sUnary sturmRoute
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed sturmUnary rUnary rootRoute
  have sealUnaryFromRoot : UnaryHistory sealRead :=
    unary_cont_closed rootUnary eUnary rootSealRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed sealUnaryFromRoot hUnary handoffRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed sealUnary hUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            WronskianObligationRowSpec F D J Omega S R E H C P N row ∨
              hsame row determinantRead ∨ hsame row valueRead ∨ hsame row sealRead ∨
                hsame row witnessRead ∨ hsame row sturmRead ∨ hsame row rootRead ∨
                  hsame row handoffRead ∨ hsame row publicRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := ⟨publicRead, hsame_refl publicRead, publicUnary⟩
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
  exact ⟨cert, witnessUnary, handoffUnary, publicUnary⟩

end BEDC.Derived.WronskianUp
