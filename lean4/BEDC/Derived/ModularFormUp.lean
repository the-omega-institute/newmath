import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.ModularFormUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem ModularFormAutomorphicTransport_stability
    {hol hol' auto auto' coeff coeff' transform transform' ledger ledger' endpoint endpoint' :
      BHist} :
    UnaryHistory hol -> UnaryHistory auto -> UnaryHistory coeff -> UnaryHistory transform ->
      hsame hol hol' -> hsame auto auto' -> hsame coeff coeff' ->
        hsame transform transform' -> Cont hol coeff ledger -> Cont hol' coeff' ledger' ->
          Cont auto transform endpoint -> Cont auto' transform' endpoint' ->
            UnaryHistory hol' ∧ UnaryHistory auto' ∧ UnaryHistory coeff' ∧
              UnaryHistory transform' ∧ UnaryHistory ledger' ∧ UnaryHistory endpoint' ∧
                hsame ledger ledger' ∧ hsame endpoint endpoint' := by
  intro holUnary autoUnary coeffUnary transformUnary sameHol sameAuto sameCoeff sameTransform
    ledgerCont ledgerCont' endpointCont endpointCont'
  have holUnary' : UnaryHistory hol' :=
    unary_transport holUnary sameHol
  have autoUnary' : UnaryHistory auto' :=
    unary_transport autoUnary sameAuto
  have coeffUnary' : UnaryHistory coeff' :=
    unary_transport coeffUnary sameCoeff
  have transformUnary' : UnaryHistory transform' :=
    unary_transport transformUnary sameTransform
  have ledgerUnary' : UnaryHistory ledger' :=
    unary_cont_closed holUnary' coeffUnary' ledgerCont'
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed autoUnary' transformUnary' endpointCont'
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameHol sameCoeff ledgerCont ledgerCont'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameAuto sameTransform endpointCont endpointCont'
  exact And.intro holUnary'
    (And.intro autoUnary'
      (And.intro coeffUnary'
        (And.intro transformUnary'
          (And.intro ledgerUnary'
            (And.intro endpointUnary'
              (And.intro sameLedger sameEndpoint))))))

def ModularFormQExpansionCarrier
    (holomorphic automorphic coefficient transform provenance ledger : BHist) : Prop :=
  UnaryHistory holomorphic ∧
    UnaryHistory automorphic ∧
      UnaryHistory coefficient ∧
        UnaryHistory transform ∧
          Cont holomorphic coefficient provenance ∧
            Cont automorphic transform ledger ∧ Cont provenance transform ledger

theorem ModularFormQExpansionCarrier_holomorphic_source_scope
    {holomorphic automorphic coefficient transform provenance ledger : BHist} :
    ModularFormQExpansionCarrier holomorphic automorphic coefficient transform provenance ledger ->
      UnaryHistory holomorphic ∧
        UnaryHistory automorphic ∧
          UnaryHistory coefficient ∧
            Cont holomorphic coefficient provenance ∧ Cont automorphic transform ledger := by
  intro carrier
  exact
    And.intro carrier.left
      (And.intro carrier.right.left
        (And.intro carrier.right.right.left
          (And.intro carrier.right.right.right.right.left
            carrier.right.right.right.right.right.left)))

theorem ModularFormQExpansionCarrier_namecert_obligation_surface
    {holomorphic automorphic coefficient transform provenance ledger endpoint : BHist} :
    ModularFormQExpansionCarrier holomorphic automorphic coefficient transform provenance ledger ->
      Cont provenance ledger endpoint ->
        SemanticNameCert (fun h : BHist => hsame h endpoint)
          (fun h : BHist => hsame h endpoint ∧ UnaryHistory h)
          (fun h : BHist =>
            hsame h endpoint ∧ Cont holomorphic coefficient provenance ∧
              Cont automorphic transform ledger ∧ Cont provenance ledger endpoint)
          hsame := by
  intro carrier endpointRow
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed carrier.left carrier.right.right.left carrier.right.right.right.right.left
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed carrier.right.left carrier.right.right.right.left
      carrier.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed provenanceUnary ledgerUnary endpointRow
  exact {
    core := {
      carrier_inhabited := Exists.intro endpoint (hsame_refl endpoint)
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row other target sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row other sameRows rowSource
        exact hsame_trans (hsame_symm sameRows) rowSource
    }
    pattern_sound := by
      intro row source
      exact And.intro source (unary_transport endpointUnary (hsame_symm source))
    ledger_sound := by
      intro row source
      exact
        And.intro source
          (And.intro carrier.right.right.right.right.left
            (And.intro carrier.right.right.right.right.right.left endpointRow))
  }

theorem ModularFormQExpansionCarrier_semantic_name_certificate
    {holomorphic automorphic coefficient transform provenance ledger : BHist} :
    ModularFormQExpansionCarrier holomorphic automorphic coefficient transform provenance
        ledger ->
      SemanticNameCert
        (fun row : BHist =>
          ModularFormQExpansionCarrier holomorphic automorphic coefficient transform provenance
            ledger ∧ hsame row ledger)
        (fun row : BHist =>
          ModularFormQExpansionCarrier holomorphic automorphic coefficient transform provenance
            ledger ∧ hsame row ledger)
        (fun row : BHist =>
          ModularFormQExpansionCarrier holomorphic automorphic coefficient transform provenance
            ledger ∧ hsame row ledger)
        hsame := by
  intro carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro ledger (And.intro carrier (hsame_refl ledger))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

end BEDC.Derived.ModularFormUp
