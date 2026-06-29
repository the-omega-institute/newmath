import BEDC.Derived.WronskianUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.WronskianUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem WronskianCarrier_linear_dependence_witness [AskSetup] [PackageSetup]
    {F D J Omega S R E H C P N determinantRead valueRead sealRead witnessRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    WronskianObligationRowSpec F D J Omega S R E H C P N J →
      WronskianObligationRowSpec F D J Omega S R E H C P N Omega →
        UnaryHistory F →
          UnaryHistory D →
            UnaryHistory J →
              UnaryHistory Omega →
                UnaryHistory S →
                  UnaryHistory R →
                    UnaryHistory E →
                      UnaryHistory P →
                        UnaryHistory N →
                          Cont F D J →
                            Cont J Omega determinantRead →
                              Cont S R valueRead →
                                Cont valueRead E sealRead →
                                  Cont determinantRead sealRead witnessRead →
                                    PkgSig bundle witnessRead pkg →
                                      SemanticNameCert
                                          (fun row : BHist =>
                                            hsame row witnessRead ∧ UnaryHistory row)
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
                                                      PkgSig bundle witnessRead pkg)
                                          hsame ∧
                                        UnaryHistory determinantRead ∧
                                          UnaryHistory valueRead ∧
                                            UnaryHistory sealRead ∧
                                              UnaryHistory witnessRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert UnaryHistory
  intro _jetSpec _omegaSpec fUnary _dUnary jUnary omegaUnary sUnary rUnary eUnary
    _pUnary _nUnary familyRoute determinantRoute valueRoute sealRoute witnessRoute
    witnessPkg
  have determinantUnary : UnaryHistory determinantRead :=
    unary_cont_closed jUnary omegaUnary determinantRoute
  have valueUnary : UnaryHistory valueRead :=
    unary_cont_closed sUnary rUnary valueRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed valueUnary eUnary sealRoute
  have witnessUnary : UnaryHistory witnessRead :=
    unary_cont_closed determinantUnary sealUnary witnessRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row witnessRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row F ∨ hsame row D ∨ hsame row J ∨ hsame row Omega ∨
              hsame row determinantRead ∨ hsame row valueRead ∨
                hsame row sealRead ∨ hsame row witnessRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont F D J ∧ Cont J Omega determinantRead ∧
              Cont S R valueRead ∧ Cont valueRead E sealRead ∧
                Cont determinantRead sealRead witnessRead ∧
                  PkgSig bundle witnessRead pkg)
          hsame := {
    core := {
      carrier_inhabited := ⟨witnessRead, hsame_refl witnessRead, witnessUnary⟩
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
        ⟨source.right, familyRoute, determinantRoute, valueRoute, sealRoute,
          witnessRoute, witnessPkg⟩
  }
  exact ⟨cert, determinantUnary, valueUnary, sealUnary, witnessUnary⟩

end BEDC.Derived.WronskianUp
