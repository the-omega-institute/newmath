import BEDC.Derived.CompactIntervalFixedPointUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CompactIntervalFixedPointUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactIntervalFixedPointCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {J G R B W Q E H C P N mapRead returnRead bisectionRead windowRead readbackRead
      sealRead localRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory J →
      UnaryHistory G →
        UnaryHistory R →
          UnaryHistory B →
            UnaryHistory W →
              UnaryHistory Q →
                UnaryHistory E →
                  UnaryHistory H →
                    UnaryHistory C →
                      UnaryHistory P →
                        UnaryHistory N →
                          hsame H N →
                            PkgSig bundle P pkg →
                              Cont J G mapRead →
                                Cont mapRead R returnRead →
                                  Cont returnRead B bisectionRead →
                                    Cont B W windowRead →
                                      Cont W Q readbackRead →
                                        Cont readbackRead E sealRead →
                                          Cont H C localRead →
                                            PkgSig bundle localRead pkg →
                                              SemanticNameCert
                                                  (fun row : BHist =>
                                                    hsame row localRead ∧
                                                      UnaryHistory row)
                                                  (fun row : BHist =>
                                                    hsame row J ∨ hsame row G ∨
                                                      hsame row R ∨ hsame row B ∨
                                                        hsame row W ∨ hsame row Q ∨
                                                          hsame row E ∨ hsame row H ∨
                                                            hsame row C ∨ hsame row P ∨
                                                              hsame row N ∨
                                                                hsame row localRead)
                                                  (fun row : BHist =>
                                                    UnaryHistory row ∧
                                                      Cont J G mapRead ∧
                                                        Cont mapRead R returnRead ∧
                                                          Cont returnRead B
                                                            bisectionRead ∧
                                                            Cont B W windowRead ∧
                                                              Cont W Q readbackRead ∧
                                                                Cont readbackRead E
                                                                  sealRead ∧
                                                                  Cont H C localRead ∧
                                                                    PkgSig bundle P pkg ∧
                                                                      PkgSig bundle
                                                                        localRead pkg)
                                                  hsame ∧
                                                UnaryHistory mapRead ∧
                                                  UnaryHistory returnRead ∧
                                                    UnaryHistory bisectionRead ∧
                                                      UnaryHistory windowRead ∧
                                                        UnaryHistory readbackRead ∧
                                                          UnaryHistory sealRead ∧
                                                            UnaryHistory localRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro jUnary gUnary rUnary bUnary wUnary qUnary eUnary hUnary _cUnary _pUnary _nUnary
    _sameHN pkgP mapRoute returnRoute bisectionRoute windowRoute readbackRoute sealRoute
    localRoute pkgLocal
  have mapUnary : UnaryHistory mapRead :=
    unary_cont_closed jUnary gUnary mapRoute
  have returnUnary : UnaryHistory returnRead :=
    unary_cont_closed mapUnary rUnary returnRoute
  have bisectionUnary : UnaryHistory bisectionRead :=
    unary_cont_closed returnUnary bUnary bisectionRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed bUnary wUnary windowRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed wUnary qUnary readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary eUnary sealRoute
  have localUnary : UnaryHistory localRead :=
    unary_cont_closed hUnary _cUnary localRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row localRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row J ∨ hsame row G ∨ hsame row R ∨ hsame row B ∨
              hsame row W ∨ hsame row Q ∨ hsame row E ∨ hsame row H ∨
                hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row localRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont J G mapRead ∧ Cont mapRead R returnRead ∧
              Cont returnRead B bisectionRead ∧ Cont B W windowRead ∧
                Cont W Q readbackRead ∧ Cont readbackRead E sealRead ∧
                  Cont H C localRead ∧ PkgSig bundle P pkg ∧
                    PkgSig bundle localRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro localRead ⟨hsame_refl localRead, localUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr source.left))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, mapRoute, returnRoute, bisectionRoute, windowRoute,
          readbackRoute, sealRoute, localRoute, pkgP, pkgLocal⟩
  }
  exact
    ⟨cert, mapUnary, returnUnary, bisectionUnary, windowUnary, readbackUnary,
      sealUnary, localUnary⟩

end BEDC.Derived.CompactIntervalFixedPointUp
