import BEDC.Derived.InscribedRouteUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.InscribedRouteUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem InscribedRouteCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {S G M R A U L P N routeRead acceptedRead consumerRead ledgerRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory S →
      UnaryHistory G →
        UnaryHistory M →
          UnaryHistory R →
            UnaryHistory A →
              UnaryHistory U →
                UnaryHistory L →
                  UnaryHistory N →
                    Cont S G routeRead →
                      Cont routeRead M acceptedRead →
                        Cont R A consumerRead →
                          Cont consumerRead U ledgerRead →
                            Cont ledgerRead N namedRead →
                              PkgSig bundle namedRead pkg →
                                SemanticNameCert
                                    (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row S ∨ hsame row G ∨ hsame row M ∨
                                        hsame row R ∨ hsame row A ∨ hsame row U ∨
                                          hsame row L ∨ hsame row namedRead)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ Cont S G routeRead ∧
                                        Cont routeRead M acceptedRead ∧
                                          Cont R A consumerRead ∧
                                            Cont consumerRead U ledgerRead ∧
                                              Cont ledgerRead N namedRead ∧
                                                PkgSig bundle namedRead pkg)
                                    hsame ∧
                                  UnaryHistory routeRead ∧ UnaryHistory acceptedRead ∧
                                    UnaryHistory consumerRead ∧ UnaryHistory ledgerRead ∧
                                      UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro sUnary gUnary mUnary rUnary aUnary uUnary _lUnary nUnary routeCont acceptedCont
    consumerCont ledgerCont namedCont namedPkg
  have routeUnary : UnaryHistory routeRead :=
    unary_cont_closed sUnary gUnary routeCont
  have acceptedUnary : UnaryHistory acceptedRead :=
    unary_cont_closed routeUnary mUnary acceptedCont
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed rUnary aUnary consumerCont
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed consumerUnary uUnary ledgerCont
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed ledgerUnary nUnary namedCont
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row G ∨ hsame row M ∨ hsame row R ∨ hsame row A ∨
              hsame row U ∨ hsame row L ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S G routeRead ∧ Cont routeRead M acceptedRead ∧
              Cont R A consumerRead ∧ Cont consumerRead U ledgerRead ∧
                Cont ledgerRead N namedRead ∧ PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, routeCont, acceptedCont, consumerCont, ledgerCont, namedCont,
          namedPkg⟩
  }
  exact ⟨cert, routeUnary, acceptedUnary, consumerUnary, ledgerUnary, namedUnary⟩

end BEDC.Derived.InscribedRouteUp
