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

theorem WronskianCarrier_ledger_exactness [AskSetup] [PackageSetup]
    {F D J Omega S R E H C P N determinantRead valueRead sealRead ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    WronskianObligationRowSpec F D J Omega S R E H C P N F →
      WronskianObligationRowSpec F D J Omega S R E H C P N D →
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
                            Cont F D J →
                              Cont J Omega determinantRead →
                                Cont S R valueRead →
                                  Cont valueRead E sealRead →
                                    Cont sealRead P ledgerRead →
                                      PkgSig bundle ledgerRead pkg →
                                        SemanticNameCert
                                            (fun row : BHist =>
                                              hsame row ledgerRead ∧ UnaryHistory row)
                                            (fun row : BHist =>
                                              hsame row F ∨ hsame row D ∨ hsame row J ∨
                                                hsame row Omega ∨ hsame row S ∨
                                                  hsame row R ∨ hsame row E ∨
                                                    hsame row ledgerRead)
                                            (fun row : BHist =>
                                              UnaryHistory row ∧ Cont F D J ∧
                                                Cont J Omega determinantRead ∧
                                                  Cont S R valueRead ∧
                                                    Cont valueRead E sealRead ∧
                                                      Cont sealRead P ledgerRead ∧
                                                        PkgSig bundle ledgerRead pkg)
                                            hsame ∧
                                          UnaryHistory determinantRead ∧
                                            UnaryHistory valueRead ∧
                                              UnaryHistory sealRead ∧
                                                UnaryHistory ledgerRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert UnaryHistory
  intro _fSpec _dSpec _jSpec _omegaSpec fUnary dUnary jUnary omegaUnary sUnary rUnary
    eUnary pUnary familyRoute determinantRoute valueRoute sealRoute ledgerRoute ledgerPkg
  have determinantUnary : UnaryHistory determinantRead :=
    unary_cont_closed jUnary omegaUnary determinantRoute
  have valueUnary : UnaryHistory valueRead :=
    unary_cont_closed sUnary rUnary valueRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed valueUnary eUnary sealRoute
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed sealUnary pUnary ledgerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row F ∨ hsame row D ∨ hsame row J ∨ hsame row Omega ∨
              hsame row S ∨ hsame row R ∨ hsame row E ∨ hsame row ledgerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont F D J ∧ Cont J Omega determinantRead ∧
              Cont S R valueRead ∧ Cont valueRead E sealRead ∧
                Cont sealRead P ledgerRead ∧ PkgSig bundle ledgerRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro ledgerRead ⟨hsame_refl ledgerRead, ledgerUnary⟩
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
          ledgerRoute, ledgerPkg⟩
  }
  exact ⟨cert, determinantUnary, valueUnary, sealUnary, ledgerUnary⟩

end BEDC.Derived.WronskianUp
