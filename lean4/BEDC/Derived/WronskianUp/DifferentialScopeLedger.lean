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

theorem WronskianCarrier_differential_scope_ledger [AskSetup] [PackageSetup]
    {F D J Omega S R E H C P N determinantRead valueRead sealRead witnessRead publicRead
      sturmRead rootRead sturmSeal sturmHandoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
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
                                            Cont sealRead H publicRead →
                                              Cont Omega S sturmRead →
                                                Cont sturmRead R rootRead →
                                                  Cont rootRead E sturmSeal →
                                                    Cont sturmSeal H sturmHandoff →
                                                      PkgSig bundle witnessRead pkg →
                                                        PkgSig bundle publicRead pkg →
                                                          PkgSig bundle sturmHandoff pkg →
                                                            exists row : BHist,
                                                              PkgSig bundle row pkg ∧
                                                                UnaryHistory row ∧
                                                                  SemanticNameCert
                                                                      (fun r : BHist =>
                                                                        hsame r witnessRead ∧
                                                                          UnaryHistory r)
                                                                      (fun r : BHist =>
                                                                        hsame r F ∨
                                                                          hsame r D ∨
                                                                            hsame r J ∨
                                                                              hsame r Omega ∨
                                                                                hsame r
                                                                                  determinantRead ∨
                                                                                  hsame r
                                                                                    valueRead ∨
                                                                                    hsame r
                                                                                      sealRead ∨
                                                                                      hsame r
                                                                                        witnessRead)
                                                                      (fun r : BHist =>
                                                                        UnaryHistory r ∧
                                                                          Cont F D J ∧
                                                                            Cont J Omega
                                                                              determinantRead ∧
                                                                              Cont S R
                                                                                valueRead ∧
                                                                                Cont valueRead E
                                                                                  sealRead ∧
                                                                                  Cont
                                                                                    determinantRead
                                                                                    sealRead
                                                                                    witnessRead ∧
                                                                                    PkgSig bundle
                                                                                      witnessRead
                                                                                      pkg)
                                                                      hsame ∧
                                                                    SemanticNameCert
                                                                      (fun r : BHist =>
                                                                        hsame r sturmHandoff ∧
                                                                          UnaryHistory r)
                                                                      (fun r : BHist =>
                                                                        hsame r Omega ∨
                                                                          hsame r S ∨
                                                                            hsame r R ∨
                                                                              hsame r E ∨
                                                                                hsame r H ∨
                                                                                  hsame r
                                                                                    sturmRead ∨
                                                                                    hsame r
                                                                                      rootRead ∨
                                                                                      hsame r
                                                                                        sturmSeal ∨
                                                                                        hsame r
                                                                                          sturmHandoff)
                                                                      (fun r : BHist =>
                                                                        UnaryHistory r ∧
                                                                          Cont Omega S
                                                                            sturmRead ∧
                                                                            Cont sturmRead R
                                                                              rootRead ∧
                                                                              Cont rootRead E
                                                                                sturmSeal ∧
                                                                                Cont sturmSeal H
                                                                                  sturmHandoff ∧
                                                                                  PkgSig bundle
                                                                                    sturmHandoff
                                                                                    pkg)
                                                                      hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert UnaryHistory
  intro dSpec jSpec omegaSpec eSpec fUnary dUnary jUnary omegaUnary sUnary rUnary
    eUnary hUnary cUnary pUnary nUnary familyRoute determinantRoute valueRoute sealRoute
    witnessRoute publicRoute sturmRoute rootRoute sturmSealRoute sturmHandoffRoute
    witnessPkg publicPkg sturmPkg
  have valueUnary : UnaryHistory valueRead :=
    unary_cont_closed sUnary rUnary valueRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed valueUnary eUnary sealRoute
  have determinantUnary : UnaryHistory determinantRead :=
    unary_cont_closed jUnary omegaUnary determinantRoute
  have witnessUnary : UnaryHistory witnessRead :=
    unary_cont_closed determinantUnary sealUnary witnessRoute
  have scopedResult :=
    WronskianCarrier_obligation_closure_scope
      (F := F) (D := D) (J := J) (Omega := Omega) (S := S) (R := R) (E := E)
      (H := H) (C := C) (P := P) (N := N) (determinantRead := determinantRead)
      (valueRead := valueRead) (sealRead := sealRead) (witnessRead := witnessRead)
      (publicRead := publicRead) (bundle := bundle) (pkg := pkg) dSpec jSpec omegaSpec
      eSpec fUnary dUnary jUnary omegaUnary sUnary rUnary eUnary hUnary cUnary pUnary
      nUnary familyRoute determinantRoute valueRoute sealRoute witnessRoute publicRoute
      witnessPkg publicPkg
  have sturm :=
    WronskianCarrier_sturm_separation_handoff
      (F := F) (D := D) (J := J) (Omega := Omega) (S := S) (R := R) (E := E)
      (H := H) (C := C) (P := P) (N := N) (sturmRead := sturmRead)
      (rootRead := rootRead) (sealRead := sturmSeal) (handoffRead := sturmHandoff)
      (bundle := bundle) (pkg := pkg) omegaSpec omegaUnary sUnary rUnary eUnary hUnary
      sturmRoute rootRoute sturmSealRoute sturmHandoffRoute sturmPkg
  exact ⟨witnessRead, witnessPkg, witnessUnary, scopedResult.left, sturm.left⟩

end BEDC.Derived.WronskianUp
