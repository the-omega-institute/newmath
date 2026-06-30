import BEDC.Derived.WronskianUp.LinearDependenceWitness
import BEDC.Derived.WronskianUp.RealSealNonescape

namespace BEDC.Derived.WronskianUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem WronskianCarrier_obligation_closure_scope [AskSetup] [PackageSetup]
    {F D J Omega S R E H C P N determinantRead valueRead sealRead witnessRead
      publicRead : BHist}
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
                                              PkgSig bundle witnessRead pkg →
                                                PkgSig bundle publicRead pkg →
                                                  SemanticNameCert
                                                      (fun row : BHist =>
                                                        hsame row witnessRead ∧
                                                          UnaryHistory row)
                                                      (fun row : BHist =>
                                                        hsame row F ∨ hsame row D ∨
                                                          hsame row J ∨ hsame row Omega ∨
                                                            hsame row determinantRead ∨
                                                              hsame row valueRead ∨
                                                                hsame row sealRead ∨
                                                                  hsame row witnessRead)
                                                      (fun row : BHist =>
                                                        UnaryHistory row ∧ Cont F D J ∧
                                                          Cont J Omega determinantRead ∧
                                                            Cont S R valueRead ∧
                                                              Cont valueRead E sealRead ∧
                                                                Cont determinantRead sealRead
                                                                  witnessRead ∧
                                                                  PkgSig bundle witnessRead
                                                                    pkg)
                                                      hsame ∧
                                                    SemanticNameCert
                                                      (fun row : BHist =>
                                                        hsame row publicRead ∧
                                                          UnaryHistory row)
                                                      (fun row : BHist =>
                                                        hsame row S ∨ hsame row R ∨
                                                          hsame row E ∨ hsame row H ∨
                                                            hsame row C ∨ hsame row P ∨
                                                              hsame row N ∨
                                                                hsame row valueRead ∨
                                                                  hsame row sealRead ∨
                                                                    hsame row publicRead)
                                                      (fun row : BHist =>
                                                        UnaryHistory row ∧ Cont S R valueRead ∧
                                                          Cont valueRead E sealRead ∧
                                                            Cont sealRead H publicRead ∧
                                                              PkgSig bundle publicRead pkg)
                                                      hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert
  intro _dSpec jSpec omegaSpec eSpec fUnary _dUnary jUnary omegaUnary sUnary rUnary
    eUnary hUnary _cUnary _pUnary nUnary familyRoute determinantRoute valueRoute
    sealRoute witnessRoute publicRoute witnessPkg publicPkg
  have witnessResult :=
    WronskianCarrier_linear_dependence_witness
      (F := F) (D := D) (J := J) (Omega := Omega) (S := S) (R := R) (E := E)
      (H := H) (C := C) (P := P) (N := N) (determinantRead := determinantRead)
      (valueRead := valueRead) (sealRead := sealRead) (witnessRead := witnessRead)
      (bundle := bundle) (pkg := pkg) jSpec omegaSpec fUnary _dUnary jUnary omegaUnary
      sUnary rUnary eUnary _pUnary nUnary familyRoute determinantRoute valueRoute
      sealRoute witnessRoute witnessPkg
  have publicResult :=
    WronskianCarrier_real_seal_nonescape
      (F := F) (D := D) (J := J) (Omega := Omega) (S := S) (R := R) (E := E)
      (H := H) (C := C) (P := P) (N := N) (valueRead := valueRead)
      (sealRead := sealRead) (publicRead := publicRead) (bundle := bundle)
      (pkg := pkg) eSpec sUnary rUnary eUnary hUnary _cUnary _pUnary nUnary valueRoute
      sealRoute publicRoute publicPkg
  exact ⟨witnessResult.left, publicResult.left⟩

end BEDC.Derived.WronskianUp
