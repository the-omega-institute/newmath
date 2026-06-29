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

theorem WronskianCarrier_real_seal_nonescape [AskSetup] [PackageSetup]
    {F D J Omega S R E H C P N valueRead sealRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    WronskianObligationRowSpec F D J Omega S R E H C P N E →
      UnaryHistory S →
        UnaryHistory R →
          UnaryHistory E →
            UnaryHistory H →
              UnaryHistory C →
                UnaryHistory P →
                  UnaryHistory N →
                    Cont S R valueRead →
                      Cont valueRead E sealRead →
                        Cont sealRead H publicRead →
                          PkgSig bundle publicRead pkg →
                            SemanticNameCert
                                (fun row : BHist =>
                                  hsame row publicRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row S ∨ hsame row R ∨ hsame row E ∨
                                    hsame row H ∨ hsame row C ∨ hsame row P ∨
                                      hsame row N ∨ hsame row valueRead ∨
                                        hsame row sealRead ∨ hsame row publicRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont S R valueRead ∧
                                    Cont valueRead E sealRead ∧
                                      Cont sealRead H publicRead ∧
                                        PkgSig bundle publicRead pkg)
                                hsame ∧
                              UnaryHistory valueRead ∧ UnaryHistory sealRead ∧
                                UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert UnaryHistory
  intro _sealSpec sUnary rUnary eUnary hUnary _cUnary _pUnary _nUnary valueRoute
    sealRoute publicRoute publicPkg
  have valueUnary : UnaryHistory valueRead :=
    unary_cont_closed sUnary rUnary valueRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed valueUnary eUnary sealRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed sealUnary hUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row R ∨ hsame row E ∨ hsame row H ∨
              hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row valueRead ∨
                hsame row sealRead ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S R valueRead ∧ Cont valueRead E sealRead ∧
              Cont sealRead H publicRead ∧ PkgSig bundle publicRead pkg)
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
      exact ⟨source.right, valueRoute, sealRoute, publicRoute, publicPkg⟩
  }
  exact ⟨cert, valueUnary, sealUnary, publicUnary⟩

end BEDC.Derived.WronskianUp
