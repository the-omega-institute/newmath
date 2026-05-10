import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Sig
import BEDC.FKernel.Unary

namespace BEDC.Derived.SolvableRadicalsUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem SolvableRadicalsTowerStepLedger_assoc_surface
    {base towerStep radicand radicalStep splitting topField towerSurface : BHist} :
    UnaryHistory base -> UnaryHistory towerStep -> UnaryHistory radicand ->
      UnaryHistory splitting -> Cont base towerStep radicalStep ->
        Cont radicalStep radicand topField -> Cont topField splitting towerSurface ->
          ∃ adjacentRow : BHist,
            Cont towerStep radicand adjacentRow ∧ Cont base adjacentRow topField ∧
              Cont topField splitting towerSurface ∧ UnaryHistory radicalStep ∧
                UnaryHistory adjacentRow ∧ UnaryHistory topField ∧
                  UnaryHistory towerSurface ∧ hsame radicalStep (append base towerStep) ∧
                    hsame adjacentRow (append towerStep radicand) ∧
                      hsame topField (append radicalStep radicand) ∧
                        hsame towerSurface (append topField splitting) := by
  intro baseUnary towerUnary radicandUnary splittingUnary radicalRow topFieldRow surfaceRow
  have radicalUnary : UnaryHistory radicalStep :=
    unary_cont_closed baseUnary towerUnary radicalRow
  have topUnary : UnaryHistory topField :=
    unary_cont_closed radicalUnary radicandUnary topFieldRow
  have surfaceUnary : UnaryHistory towerSurface :=
    unary_cont_closed topUnary splittingUnary surfaceRow
  cases cont_assoc_left_exists radicalRow topFieldRow with
  | intro adjacentRow adjacentData =>
      have adjacentUnary : UnaryHistory adjacentRow :=
        unary_cont_closed towerUnary radicandUnary adjacentData.left
      exact Exists.intro adjacentRow
        (And.intro adjacentData.left
          (And.intro adjacentData.right
            (And.intro surfaceRow
              (And.intro radicalUnary
                (And.intro adjacentUnary
                  (And.intro topUnary
                    (And.intro surfaceUnary
                      (And.intro radicalRow
                        (And.intro adjacentData.left
                          (And.intro topFieldRow surfaceRow))))))))))

theorem SolvableRadicalsTowerStep_obligation
    {baseField nextField rootIndex radicand stepExtension towerLedger : BHist} :
    UnaryHistory baseField ->
      UnaryHistory nextField ->
        UnaryHistory rootIndex ->
          UnaryHistory radicand ->
            Cont rootIndex radicand stepExtension ->
              Cont baseField nextField towerLedger ->
                UnaryHistory stepExtension ∧ UnaryHistory towerLedger ∧
                  hsame stepExtension (append rootIndex radicand) ∧
                    hsame towerLedger (append baseField nextField) := by
  intro baseUnary nextUnary rootUnary radicandUnary stepRow towerRow
  have stepUnary : UnaryHistory stepExtension :=
    unary_cont_closed rootUnary radicandUnary stepRow
  have towerUnary : UnaryHistory towerLedger :=
    unary_cont_closed baseUnary nextUnary towerRow
  constructor
  · exact stepUnary
  constructor
  · exact towerUnary
  constructor
  · exact stepRow
  · exact towerRow

def SolvableRadicalsTowerPacket [AskSetup] [PackageSetup]
    (towerDepth intermediateFields rootIndices radicands basePolynomial splittingVerdict
      towerLedger stepLedger endpoint provenance : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory towerDepth ∧
    UnaryHistory intermediateFields ∧
      UnaryHistory rootIndices ∧
        UnaryHistory radicands ∧
          UnaryHistory basePolynomial ∧
            UnaryHistory splittingVerdict ∧
              Cont towerDepth intermediateFields towerLedger ∧
                Cont rootIndices radicands stepLedger ∧
                  Cont towerLedger stepLedger endpoint ∧
                    SigRel bundle endpoint provenance ∧
                      PkgSig bundle provenance pkg

theorem SolvableRadicalsTowerPacket_intermediate_field_stability
    [AskSetup] [PackageSetup]
    {towerDepth towerDepth' intermediateFields intermediateFields' rootIndices rootIndices'
      radicands radicands' basePolynomial splittingVerdict towerLedger towerLedger' stepLedger
      stepLedger' endpoint endpoint' provenance provenance' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SolvableRadicalsTowerPacket towerDepth intermediateFields rootIndices radicands
      basePolynomial splittingVerdict towerLedger stepLedger endpoint provenance bundle pkg ->
        SolvableRadicalsTowerPacket towerDepth' intermediateFields' rootIndices' radicands'
          basePolynomial splittingVerdict towerLedger' stepLedger' endpoint' provenance' bundle
          pkg ->
          hsame towerDepth towerDepth' ->
            hsame intermediateFields intermediateFields' ->
              hsame rootIndices rootIndices' ->
                hsame radicands radicands' ->
                  hsame towerLedger towerLedger' ∧
                    hsame stepLedger stepLedger' ∧
                      hsame endpoint endpoint' ∧
                        UnaryHistory towerLedger' ∧
                          UnaryHistory stepLedger' ∧
                            UnaryHistory endpoint' := by
  intro leftPacket rightPacket sameDepth sameFields sameRoots sameRadicands
  have towerSame : hsame towerLedger towerLedger' :=
    cont_respects_hsame sameDepth sameFields
      leftPacket.right.right.right.right.right.right.left
      rightPacket.right.right.right.right.right.right.left
  have stepSame : hsame stepLedger stepLedger' :=
    cont_respects_hsame sameRoots sameRadicands
      leftPacket.right.right.right.right.right.right.right.left
      rightPacket.right.right.right.right.right.right.right.left
  have endpointSame : hsame endpoint endpoint' :=
    cont_respects_hsame towerSame stepSame
      leftPacket.right.right.right.right.right.right.right.right.left
      rightPacket.right.right.right.right.right.right.right.right.left
  have towerUnary : UnaryHistory towerLedger' :=
    unary_cont_closed rightPacket.left rightPacket.right.left
      rightPacket.right.right.right.right.right.right.left
  have stepUnary : UnaryHistory stepLedger' :=
    unary_cont_closed rightPacket.right.right.left rightPacket.right.right.right.left
      rightPacket.right.right.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint' :=
    unary_cont_closed towerUnary stepUnary
      rightPacket.right.right.right.right.right.right.right.right.left
  exact And.intro towerSame
    (And.intro stepSame
      (And.intro endpointSame
        (And.intro towerUnary (And.intro stepUnary endpointUnary))))

theorem SolvableRadicalsTowerPacket_splitting_ledger_exactness
    [AskSetup] [PackageSetup]
    {towerDepth intermediateFields rootIndices radicands basePolynomial splittingVerdict
      towerLedger stepLedger endpoint provenance splittingLedger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SolvableRadicalsTowerPacket towerDepth intermediateFields rootIndices radicands
        basePolynomial splittingVerdict towerLedger stepLedger endpoint provenance bundle pkg ->
      Cont basePolynomial splittingVerdict splittingLedger ->
        UnaryHistory splittingLedger ∧ hsame splittingLedger (append basePolynomial splittingVerdict) ∧
          hsame endpoint (append towerLedger stepLedger) ∧ SigRel bundle endpoint provenance ∧
            PkgSig bundle provenance pkg := by
  intro packet splittingRow
  have splittingUnary : UnaryHistory splittingLedger :=
    unary_cont_closed packet.right.right.right.right.left packet.right.right.right.right.right.left
      splittingRow
  exact And.intro splittingUnary
    (And.intro splittingRow
      (And.intro packet.right.right.right.right.right.right.right.right.left
        (And.intro packet.right.right.right.right.right.right.right.right.right.left
          packet.right.right.right.right.right.right.right.right.right.right)))

end BEDC.Derived.SolvableRadicalsUp
