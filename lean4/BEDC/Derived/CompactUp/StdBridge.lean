import BEDC.Derived.CompactUp.SemanticCertificate

namespace BEDC.Derived.CompactUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CompactUp_StdBridge
    {center precision net subset located finite intermediate compact : BHist}
    (centerCarrier : UnaryHistory center) (precisionCarrier : UnaryHistory precision) :
    CompactNetWitness center precision net ->
      CompactWitnessCarrier subset located finite intermediate compact ->
        SemanticNameCert (CompactNetWitness center precision)
            (CompactNetWitness center precision) (CompactNetWitness center precision) hsame ∧
          UnaryHistory subset ∧ UnaryHistory located ∧ UnaryHistory finite ∧ UnaryHistory net ∧
            UnaryHistory compact ∧ Cont center precision net ∧
              Cont subset located intermediate ∧ Cont intermediate finite compact := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory SemanticNameCert hsame
  intro netWitness carrier
  have cert :
      SemanticNameCert (CompactNetWitness center precision)
        (CompactNetWitness center precision) (CompactNetWitness center precision) hsame :=
    CompactNetWitness_semanticNameCert centerCarrier precisionCarrier
  have subsetCarrier : UnaryHistory subset := carrier.left
  have locatedCarrier : UnaryHistory located := carrier.right.left
  have finiteCarrier : UnaryHistory finite := carrier.right.right.left
  have locatedLedger : Cont subset located intermediate := carrier.right.right.right.left
  have finiteLedger : Cont intermediate finite compact := carrier.right.right.right.right
  have intermediateCarrier : UnaryHistory intermediate :=
    unary_cont_closed subsetCarrier locatedCarrier locatedLedger
  have compactCarrier : UnaryHistory compact :=
    unary_cont_closed intermediateCarrier finiteCarrier finiteLedger
  exact And.intro cert
    (And.intro subsetCarrier
      (And.intro locatedCarrier
        (And.intro finiteCarrier
          (And.intro netWitness.right.right.left
            (And.intro compactCarrier
              (And.intro netWitness.right.right.right
                (And.intro locatedLedger finiteLedger)))))))

end BEDC.Derived.CompactUp
