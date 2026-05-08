import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.InducedRepUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem InducedRepFrobeniusLedger_boundary
    {subgroup representation induction restriction frobenius unit counit provenance ledger :
      BHist} :
    UnaryHistory subgroup ->
      UnaryHistory representation ->
        UnaryHistory induction ->
          UnaryHistory restriction ->
            UnaryHistory unit ->
              Cont subgroup representation provenance ->
                Cont induction restriction frobenius ->
                  Cont frobenius unit counit ->
                    Cont provenance counit ledger ->
                      UnaryHistory provenance ∧ UnaryHistory frobenius ∧ UnaryHistory counit ∧
                        UnaryHistory ledger ∧ hsame provenance (append subgroup representation) ∧
                          hsame frobenius (append induction restriction) ∧
                            hsame counit (append frobenius unit) ∧
                              hsame ledger (append provenance counit) := by
  intro subgroupUnary representationUnary inductionUnary restrictionUnary unitUnary provenanceCont
    frobeniusCont counitCont ledgerCont
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed subgroupUnary representationUnary provenanceCont
  have frobeniusUnary : UnaryHistory frobenius :=
    unary_cont_closed inductionUnary restrictionUnary frobeniusCont
  have counitUnary : UnaryHistory counit :=
    unary_cont_closed frobeniusUnary unitUnary counitCont
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed provenanceUnary counitUnary ledgerCont
  exact And.intro provenanceUnary
    (And.intro frobeniusUnary
      (And.intro counitUnary
        (And.intro ledgerUnary
          (And.intro provenanceCont
            (And.intro frobeniusCont
              (And.intro counitCont ledgerCont))))))

theorem InducedRepCarrierPacket_namecert_obligation_surface
    {subgroup representation induction restriction frobenius unit counit provenance ledger :
      BHist} :
    UnaryHistory subgroup ->
      UnaryHistory representation ->
        UnaryHistory induction ->
          UnaryHistory restriction ->
            UnaryHistory unit ->
              Cont subgroup representation provenance ->
                Cont induction restriction frobenius ->
                  Cont frobenius unit counit ->
                    Cont provenance counit ledger ->
                      SemanticNameCert
                          (fun row : BHist =>
                            exists frobenius counit provenance : BHist,
                              Cont induction restriction frobenius ∧
                                Cont frobenius unit counit ∧
                                  Cont provenance counit row ∧
                                    hsame provenance (append subgroup representation))
                          (fun row : BHist =>
                            exists frobenius counit provenance : BHist,
                              Cont induction restriction frobenius ∧
                                Cont frobenius unit counit ∧
                                  Cont provenance counit row ∧
                                    hsame provenance (append subgroup representation))
                          (fun row : BHist =>
                            exists frobenius counit provenance : BHist,
                              Cont induction restriction frobenius ∧
                                Cont frobenius unit counit ∧
                                  Cont provenance counit row ∧
                                    hsame provenance (append subgroup representation))
                          (fun left right : BHist =>
                            (exists frobenius counit provenance : BHist,
                              Cont induction restriction frobenius ∧
                                Cont frobenius unit counit ∧
                                  Cont provenance counit left ∧
                                    hsame provenance (append subgroup representation)) ∧
                              (exists frobenius counit provenance : BHist,
                                Cont induction restriction frobenius ∧
                                  Cont frobenius unit counit ∧
                                    Cont provenance counit right ∧
                                      hsame provenance (append subgroup representation)) ∧
                                hsame left right) ∧
                        UnaryHistory ledger ∧ hsame ledger (append provenance counit) ∧
                          hsame frobenius (append induction restriction) := by
  intro subgroupUnary representationUnary inductionUnary restrictionUnary unitUnary provenanceCont
    frobeniusCont counitCont ledgerCont
  have boundary :=
    InducedRepFrobeniusLedger_boundary subgroupUnary representationUnary inductionUnary
      restrictionUnary unitUnary provenanceCont frobeniusCont counitCont ledgerCont
  constructor
  · exact {
      core := {
        carrier_inhabited := by
          refine Exists.intro ledger ?_
          refine Exists.intro frobenius ?_
          refine Exists.intro counit ?_
          refine Exists.intro provenance ?_
          exact And.intro frobeniusCont
            (And.intro counitCont (And.intro ledgerCont provenanceCont))
        equiv_refl := by
          intro row source
          exact And.intro source (And.intro source (hsame_refl row))
        equiv_symm := by
          intro left right classified
          exact And.intro classified.right.left
            (And.intro classified.left (hsame_symm classified.right.right))
        equiv_trans := by
          intro left middle right classifiedLM classifiedMR
          exact And.intro classifiedLM.left
            (And.intro classifiedMR.right.left
              (hsame_trans classifiedLM.right.right classifiedMR.right.right))
        carrier_respects_equiv := by
          intro left right classified _source
          exact classified.right.left
      }
      pattern_sound := by
        intro row source
        exact source
      ledger_sound := by
        intro row source
        exact source
    }
  · exact And.intro boundary.right.right.right.left
      (And.intro boundary.right.right.right.right.right.right.right
        boundary.right.right.right.right.right.left)

theorem InducedRepBHistCarrier_namecert_obligation_surface
    {subgroup representation induction restriction frobenius unit counit provenance ledger surface :
      BHist} :
    UnaryHistory subgroup ->
      UnaryHistory representation ->
        UnaryHistory induction ->
          UnaryHistory restriction ->
            UnaryHistory unit ->
              Cont subgroup representation provenance ->
                Cont induction restriction frobenius ->
                  Cont frobenius unit counit ->
                    Cont provenance counit ledger ->
                      Cont ledger frobenius surface ->
                        UnaryHistory provenance ∧ UnaryHistory frobenius ∧ UnaryHistory counit ∧
                          UnaryHistory ledger ∧ UnaryHistory surface ∧
                            hsame provenance (append subgroup representation) ∧
                              hsame frobenius (append induction restriction) ∧
                                hsame counit (append frobenius unit) ∧
                                  hsame ledger (append provenance counit) ∧
                                    hsame surface (append ledger frobenius) := by
  intro subgroupUnary representationUnary inductionUnary restrictionUnary unitUnary provenanceCont
    frobeniusCont counitCont ledgerCont surfaceCont
  have boundary :=
    InducedRepFrobeniusLedger_boundary subgroupUnary representationUnary inductionUnary
      restrictionUnary unitUnary provenanceCont frobeniusCont counitCont ledgerCont
  have surfaceUnary : UnaryHistory surface :=
    unary_cont_closed boundary.right.right.right.left boundary.right.left surfaceCont
  exact And.intro boundary.left
    (And.intro boundary.right.left
      (And.intro boundary.right.right.left
        (And.intro boundary.right.right.right.left
          (And.intro surfaceUnary
            (And.intro boundary.right.right.right.right.left
              (And.intro boundary.right.right.right.right.right.left
                (And.intro boundary.right.right.right.right.right.right.left
                  (And.intro boundary.right.right.right.right.right.right.right surfaceCont))))))))

end BEDC.Derived.InducedRepUp
