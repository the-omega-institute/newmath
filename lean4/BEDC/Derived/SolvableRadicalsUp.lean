import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SolvableRadicalsUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

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

end BEDC.Derived.SolvableRadicalsUp
