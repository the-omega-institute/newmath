import BEDC.Derived.IntervalDomainUp.NameCertObligations

namespace BEDC.Derived.IntervalDomainUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem IntervalDomainEndpointDirectednessScope [AskSetup] [PackageSetup]
    {L R N W Q E H _C P A endpointRead widthRead dyadicRead refinementRead realRead
      namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory L →
      UnaryHistory R →
        UnaryHistory N →
          UnaryHistory W →
            UnaryHistory Q →
              UnaryHistory E →
                UnaryHistory A →
                  Cont L R endpointRead →
                    Cont endpointRead Q widthRead →
                      Cont widthRead W dyadicRead →
                        Cont dyadicRead N refinementRead →
                          Cont refinementRead E realRead →
                            Cont realRead A namedRead →
                              hsame H (append P A) →
                                PkgSig bundle P pkg →
                                  PkgSig bundle A pkg →
                                    SemanticNameCert
                                        (fun row : BHist =>
                                          hsame row namedRead ∧ UnaryHistory row)
                                        (fun row : BHist =>
                                          hsame row L ∨ hsame row R ∨ hsame row N ∨
                                            hsame row W ∨ hsame row Q ∨ hsame row E ∨
                                              hsame row namedRead)
                                        (fun row : BHist =>
                                          UnaryHistory row ∧ Cont L R endpointRead ∧
                                            Cont endpointRead Q widthRead ∧
                                              Cont widthRead W dyadicRead ∧
                                                Cont dyadicRead N refinementRead ∧
                                                  Cont refinementRead E realRead ∧
                                                    Cont realRead A namedRead ∧
                                                      hsame H (append P A) ∧
                                                        PkgSig bundle P pkg ∧
                                                          PkgSig bundle A pkg)
                                        hsame ∧
                                      UnaryHistory endpointRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro lUnary rUnary nUnary wUnary qUnary eUnary aUnary endpointRoute widthRoute
    dyadicRoute refinementRoute realRoute namedRoute transportSame provenancePkg namePkg
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed lUnary rUnary endpointRoute
  have widthUnary : UnaryHistory widthRead :=
    unary_cont_closed endpointUnary qUnary widthRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed widthUnary wUnary dyadicRoute
  have refinementUnary : UnaryHistory refinementRead :=
    unary_cont_closed dyadicUnary nUnary refinementRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed refinementUnary eUnary realRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed realUnary aUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row L ∨ hsame row R ∨ hsame row N ∨ hsame row W ∨ hsame row Q ∨
              hsame row E ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont L R endpointRead ∧ Cont endpointRead Q widthRead ∧
              Cont widthRead W dyadicRead ∧ Cont dyadicRead N refinementRead ∧
                Cont refinementRead E realRead ∧ Cont realRead A namedRead ∧
                  hsame H (append P A) ∧ PkgSig bundle P pkg ∧ PkgSig bundle A pkg)
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, endpointRoute, widthRoute, dyadicRoute, refinementRoute, realRoute,
          namedRoute, transportSame, provenancePkg, namePkg⟩
  }
  exact ⟨cert, endpointUnary, namedUnary⟩

end BEDC.Derived.IntervalDomainUp
