import BEDC.Derived.CompactIntervalFixedPointUp.ScopedRoute

namespace BEDC.Derived.CompactIntervalFixedPointUp.ResidualBisectionHandoff

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactIntervalFixedPoint_residual_bisection_handoff [AskSetup] [PackageSetup]
    {J G R B W Q E H C P N mapRead returnRead bisectionRead windowRead readbackRead
      sealRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory J →
      UnaryHistory G →
        UnaryHistory R →
          UnaryHistory B →
            UnaryHistory W →
              UnaryHistory Q →
                UnaryHistory E →
                  UnaryHistory N →
                    PkgSig bundle N pkg →
                      Cont J G mapRead →
                        Cont mapRead R returnRead →
                          Cont returnRead B bisectionRead →
                            Cont bisectionRead W windowRead →
                              Cont windowRead Q readbackRead →
                                Cont readbackRead E sealRead →
                                  Cont sealRead N namedRead →
                                    PkgSig bundle namedRead pkg →
                                      SemanticNameCert
                                          (fun row : BHist =>
                                            hsame row namedRead ∧ UnaryHistory row)
                                          (fun row : BHist =>
                                            hsame row J ∨ hsame row G ∨ hsame row R ∨
                                              hsame row B ∨ hsame row W ∨ hsame row Q ∨
                                                hsame row E ∨ hsame row namedRead)
                                          (fun row : BHist =>
                                            UnaryHistory row ∧ Cont J G mapRead ∧
                                              Cont mapRead R returnRead ∧
                                                Cont returnRead B bisectionRead ∧
                                                  Cont bisectionRead W windowRead ∧
                                                    Cont windowRead Q readbackRead ∧
                                                      Cont readbackRead E sealRead ∧
                                                        Cont sealRead N namedRead ∧
                                                          PkgSig bundle namedRead pkg)
                                          hsame ∧
                                        UnaryHistory bisectionRead ∧
                                          UnaryHistory windowRead ∧
                                            UnaryHistory readbackRead ∧
                                              UnaryHistory sealRead ∧
                                                UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro jUnary gUnary rUnary bUnary wUnary qUnary eUnary nUnary _namePkg mapRoute
    returnRoute bisectionRoute windowRoute readbackRoute sealRoute namedRoute namedReadPkg
  have mapUnary : UnaryHistory mapRead :=
    unary_cont_closed jUnary gUnary mapRoute
  have returnUnary : UnaryHistory returnRead :=
    unary_cont_closed mapUnary rUnary returnRoute
  have bisectionUnary : UnaryHistory bisectionRead :=
    unary_cont_closed returnUnary bUnary bisectionRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed bisectionUnary wUnary windowRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowUnary qUnary readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary eUnary sealRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed sealUnary nUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row J ∨ hsame row G ∨ hsame row R ∨ hsame row B ∨ hsame row W ∨
              hsame row Q ∨ hsame row E ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont J G mapRead ∧ Cont mapRead R returnRead ∧
              Cont returnRead B bisectionRead ∧ Cont bisectionRead W windowRead ∧
                Cont windowRead Q readbackRead ∧ Cont readbackRead E sealRead ∧
                  Cont sealRead N namedRead ∧ PkgSig bundle namedRead pkg)
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
        ⟨source.right, mapRoute, returnRoute, bisectionRoute, windowRoute, readbackRoute,
          sealRoute, namedRoute, namedReadPkg⟩
  }
  exact ⟨cert, bisectionUnary, windowUnary, readbackUnary, sealUnary, namedUnary⟩

end BEDC.Derived.CompactIntervalFixedPointUp.ResidualBisectionHandoff
