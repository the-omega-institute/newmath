import BEDC.Derived.DyadicIntervalCoverUp.RootWindowCoverage

namespace BEDC.Derived.DyadicIntervalCoverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicIntervalCoverRealSealScope [AskSetup] [PackageSetup]
    {L U M R V W Q A H C P N endpointRead windowRead readbackRead membershipRead sealRead
      namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicIntervalCoverRootObligationSurface L U M R V W Q A H C P N bundle pkg →
      Cont L U endpointRead →
        Cont W Q windowRead →
          Cont windowRead R readbackRead →
            Cont readbackRead V membershipRead →
              Cont membershipRead A sealRead →
                Cont sealRead N namedRead →
                  PkgSig bundle namedRead pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row L ∨ hsame row U ∨ hsame row W ∨ hsame row Q ∨
                            hsame row R ∨ hsame row V ∨ hsame row A ∨ hsame row N ∨
                              hsame row endpointRead ∨ hsame row windowRead ∨
                                hsame row readbackRead ∨ hsame row membershipRead ∨
                                  hsame row sealRead ∨ hsame row namedRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont L U endpointRead ∧
                            Cont W Q windowRead ∧ Cont windowRead R readbackRead ∧
                              Cont readbackRead V membershipRead ∧
                                Cont membershipRead A sealRead ∧ Cont sealRead N namedRead ∧
                                  PkgSig bundle namedRead pkg)
                        hsame ∧ UnaryHistory endpointRead ∧ UnaryHistory windowRead ∧
                      UnaryHistory readbackRead ∧ UnaryHistory membershipRead ∧
                        UnaryHistory sealRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro surface endpointRoute windowRoute readbackRoute membershipRoute sealRoute namedRoute
    namedPkg
  have lUnary : UnaryHistory L := surface.left
  have uUnary : UnaryHistory U := surface.right.left
  have rUnary : UnaryHistory R := surface.right.right.right.left
  have vUnary : UnaryHistory V := surface.right.right.right.right.left
  have wUnary : UnaryHistory W := surface.right.right.right.right.right.left
  have qUnary : UnaryHistory Q := surface.right.right.right.right.right.right.left
  have aUnary : UnaryHistory A := surface.right.right.right.right.right.right.right.left
  have nUnary : UnaryHistory N :=
    surface.right.right.right.right.right.right.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed lUnary uUnary endpointRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed wUnary qUnary windowRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowUnary rUnary readbackRoute
  have membershipUnary : UnaryHistory membershipRead :=
    unary_cont_closed readbackUnary vUnary membershipRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed membershipUnary aUnary sealRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed sealUnary nUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row L ∨ hsame row U ∨ hsame row W ∨ hsame row Q ∨ hsame row R ∨
              hsame row V ∨ hsame row A ∨ hsame row N ∨ hsame row endpointRead ∨
                hsame row windowRead ∨ hsame row readbackRead ∨
                  hsame row membershipRead ∨ hsame row sealRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont L U endpointRead ∧ Cont W Q windowRead ∧
              Cont windowRead R readbackRead ∧ Cont readbackRead V membershipRead ∧
                Cont membershipRead A sealRead ∧ Cont sealRead N namedRead ∧
                  PkgSig bundle namedRead pkg)
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr source.left))))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, endpointRoute, windowRoute, readbackRoute, membershipRoute,
          sealRoute, namedRoute, namedPkg⟩
  }
  exact
    ⟨cert, endpointUnary, windowUnary, readbackUnary, membershipUnary, sealUnary,
      namedUnary⟩

end BEDC.Derived.DyadicIntervalCoverUp
