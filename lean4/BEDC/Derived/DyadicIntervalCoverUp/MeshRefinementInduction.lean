import BEDC.Derived.DyadicIntervalCoverUp

namespace BEDC.Derived.DyadicIntervalCoverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicIntervalCoverMeshRefinementInduction [AskSetup] [PackageSetup]
    {L U M R V W Q A H C P N endpointRead meshRead membershipRead windowRead sealRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    dyadicIntervalCoverFields (DyadicIntervalCoverUp.mk L U M R V W Q A H C P N) =
        [L, U, M, R, V, W, Q, A, H, C, P, N] ->
      UnaryHistory L ->
        UnaryHistory U ->
          UnaryHistory M ->
            UnaryHistory R ->
              UnaryHistory V ->
                UnaryHistory W ->
                  UnaryHistory Q ->
                    UnaryHistory A ->
                      Cont L U endpointRead ->
                        Cont endpointRead M meshRead ->
                          Cont meshRead V membershipRead ->
                            Cont W Q windowRead ->
                              Cont membershipRead A sealRead ->
                                PkgSig bundle P pkg ->
                                  PkgSig bundle N pkg ->
                                    SemanticNameCert
                                        (fun row : BHist =>
                                          hsame row sealRead ∧ UnaryHistory row)
                                        (fun row : BHist =>
                                          hsame row L ∨ hsame row U ∨ hsame row M ∨
                                            hsame row R ∨ hsame row V ∨ hsame row W ∨
                                              hsame row Q ∨ hsame row A ∨ hsame row H ∨
                                                hsame row C ∨ hsame row P ∨ hsame row N ∨
                                                  hsame row sealRead)
                                        (fun row : BHist =>
                                          UnaryHistory row ∧ Cont L U endpointRead ∧
                                            Cont endpointRead M meshRead ∧
                                              Cont meshRead V membershipRead ∧
                                                Cont W Q windowRead ∧
                                                  Cont membershipRead A sealRead ∧
                                                    PkgSig bundle P pkg ∧
                                                      PkgSig bundle N pkg)
                                        hsame ∧
                                      UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Cont PkgSig hsame SemanticNameCert
  intro fields lUnary uUnary mUnary _rUnary vUnary wUnary qUnary aUnary endpointRoute
    meshRoute membershipRoute windowRoute sealRoute provenancePkg namePkg
  have _acceptedFields :
      dyadicIntervalCoverFields (DyadicIntervalCoverUp.mk L U M R V W Q A H C P N) =
        [L, U, M, R, V, W, Q, A, H, C, P, N] := fields
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed lUnary uUnary endpointRoute
  have meshUnary : UnaryHistory meshRead :=
    unary_cont_closed endpointUnary mUnary meshRoute
  have membershipUnary : UnaryHistory membershipRead :=
    unary_cont_closed meshUnary vUnary membershipRoute
  have _windowUnary : UnaryHistory windowRead :=
    unary_cont_closed wUnary qUnary windowRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed membershipUnary aUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row L ∨ hsame row U ∨ hsame row M ∨ hsame row R ∨ hsame row V ∨
              hsame row W ∨ hsame row Q ∨ hsame row A ∨ hsame row H ∨ hsame row C ∨
                hsame row P ∨ hsame row N ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont L U endpointRead ∧ Cont endpointRead M meshRead ∧
              Cont meshRead V membershipRead ∧ Cont W Q windowRead ∧
                Cont membershipRead A sealRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
      exact Or.inr
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
                            (Or.inr source.left)))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, endpointRoute, meshRoute, membershipRoute, windowRoute, sealRoute,
          provenancePkg, namePkg⟩
  }
  exact ⟨cert, sealUnary⟩

end BEDC.Derived.DyadicIntervalCoverUp
