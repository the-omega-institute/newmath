import BEDC.Derived.CompactUp

namespace BEDC.Derived.CompactUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def ImageLocatedRefinementLedger
    (source map target modulus epsilon delta imageSubset imageLocated imageFinite imageIntermediate
      imageCompact finalImageLocated finalImageIntermediate finalImageCompact : BHist) : Prop :=
  UnaryHistory imageSubset ∧ UnaryHistory imageLocated ∧ UnaryHistory imageFinite ∧
    Cont imageSubset imageLocated imageIntermediate ∧
      Cont imageIntermediate imageFinite imageCompact ∧
        CompactLocatedRefinementChain imageFinite imageLocated imageIntermediate imageCompact
          finalImageLocated finalImageIntermediate finalImageCompact

theorem ImageLocatedRefinementLedger_compact_carrier
    {source map target modulus epsilon delta imageSubset imageLocated imageFinite imageIntermediate
      imageCompact finalImageLocated finalImageIntermediate finalImageCompact : BHist} :
    ImageLocatedRefinementLedger source map target modulus epsilon delta imageSubset imageLocated
        imageFinite imageIntermediate imageCompact finalImageLocated finalImageIntermediate
        finalImageCompact ->
      CompactWitnessCarrier imageSubset finalImageLocated imageFinite finalImageIntermediate
        finalImageCompact := by
  intro ledger
  have initial :
      CompactWitnessCarrier imageSubset imageLocated imageFinite imageIntermediate imageCompact :=
    And.intro ledger.left
      (And.intro ledger.right.left
        (And.intro ledger.right.right.left
          (And.intro ledger.right.right.right.left ledger.right.right.right.right.left)))
  exact CompactWitnessCarrier_located_refinement_chain_closed initial
    ledger.right.right.right.right.right

end BEDC.Derived.CompactUp
