import BEDC.Derived.CompactUp
import BEDC.Derived.ContinuousMapUp
import BEDC.FKernel.Bundle

namespace BEDC.Derived.CompactUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def ImageFiniteNetLedger
    (source map target delta epsilon : BHist) (sourceBundle targetBundle : ProbeBundle BHist)
      (ledger : BHist) : Prop :=
  InBundle source sourceBundle ∧ InBundle target targetBundle ∧ UnaryHistory delta ∧
    UnaryHistory epsilon ∧ UnaryHistory ledger ∧
      BEDC.Derived.ContinuousMapUp.ContinuousMapCarrier source map target delta epsilon ledger

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

theorem ImageLocatedRefinementLedger_hsame_transport
    {source map target modulus epsilon delta imageSubset imageLocated imageFinite imageIntermediate
      imageCompact finalImageLocated finalImageIntermediate finalImageCompact imageSubset'
      imageLocated' imageFinite' imageIntermediate' imageCompact' finalImageLocated'
      finalImageIntermediate' finalImageCompact' : BHist} :
    hsame imageSubset imageSubset' -> hsame imageLocated imageLocated' ->
      hsame imageFinite imageFinite' -> hsame imageIntermediate imageIntermediate' ->
        hsame imageCompact imageCompact' -> hsame finalImageLocated finalImageLocated' ->
          hsame finalImageIntermediate finalImageIntermediate' ->
            hsame finalImageCompact finalImageCompact' ->
              ImageLocatedRefinementLedger source map target modulus epsilon delta imageSubset
                imageLocated imageFinite imageIntermediate imageCompact finalImageLocated
                finalImageIntermediate finalImageCompact ->
                ImageLocatedRefinementLedger source map target modulus epsilon delta imageSubset'
                    imageLocated' imageFinite' imageIntermediate' imageCompact' finalImageLocated'
                    finalImageIntermediate' finalImageCompact' ∧
                  CompactWitnessCarrier imageSubset' finalImageLocated' imageFinite'
                    finalImageIntermediate' finalImageCompact' ∧
                    Cont imageSubset' finalImageLocated' finalImageIntermediate' ∧
                      Cont finalImageIntermediate' imageFinite' finalImageCompact' := by
  intro sameSubset sameLocated sameFinite sameIntermediate sameCompact sameFinalLocated
    sameFinalIntermediate sameFinalCompact ledger
  cases sameSubset
  cases sameLocated
  cases sameFinite
  cases sameIntermediate
  cases sameCompact
  cases sameFinalLocated
  cases sameFinalIntermediate
  cases sameFinalCompact
  have transportedLedger :
      ImageLocatedRefinementLedger source map target modulus epsilon delta imageSubset imageLocated
        imageFinite imageIntermediate imageCompact finalImageLocated finalImageIntermediate
        finalImageCompact := ledger
  have finalCarrier :
      CompactWitnessCarrier imageSubset finalImageLocated imageFinite finalImageIntermediate
        finalImageCompact :=
    ImageLocatedRefinementLedger_compact_carrier transportedLedger
  exact And.intro transportedLedger
    (And.intro finalCarrier (And.intro finalCarrier.right.right.right.left
      finalCarrier.right.right.right.right))

end BEDC.Derived.CompactUp
