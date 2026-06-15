import BEDC.Derived.ImplicitFunctionUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ImplicitFunctionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def implicit_function_carrier_root_equation_carrier_carrier [AskSetup] [PackageSetup]
    (equation base derivative linear matrix picard graph realSeal transport replay
      provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  UnaryHistory equation ∧ UnaryHistory base ∧ UnaryHistory linear ∧
    UnaryHistory picard ∧ UnaryHistory realSeal ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
      Cont equation base derivative ∧ Cont derivative linear matrix ∧
        Cont matrix picard graph ∧ Cont graph realSeal provenance ∧
          Cont transport replay localName ∧ PkgSig bundle localName pkg

theorem ImplicitFunctionCarrier_root_equation_carrier [AskSetup] [PackageSetup]
    {equation base derivative linear matrix picard graph realSeal transport replay
      provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    implicit_function_carrier_root_equation_carrier_carrier
        equation base derivative linear matrix picard graph realSeal
        transport replay provenance localName bundle pkg ->
      UnaryHistory realSeal ∧ UnaryHistory provenance ∧
        Cont equation base derivative ∧ Cont derivative linear matrix ∧
          Cont matrix picard graph ∧ Cont graph realSeal provenance ∧
            PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier
  obtain ⟨equationUnary, baseUnary, linearUnary, picardUnary, realSealUnary, _transportUnary,
    _replayUnary, equationBaseDerivative, derivativeLinearMatrix, matrixPicardGraph,
    graphRealSealProvenance, _transportReplayLocalName, localNamePkg⟩ := carrier
  have derivativeUnary : UnaryHistory derivative :=
    unary_cont_closed equationUnary baseUnary equationBaseDerivative
  have matrixUnary : UnaryHistory matrix :=
    unary_cont_closed derivativeUnary linearUnary derivativeLinearMatrix
  have graphUnary : UnaryHistory graph :=
    unary_cont_closed matrixUnary picardUnary matrixPicardGraph
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed graphUnary realSealUnary graphRealSealProvenance
  exact
    ⟨realSealUnary, provenanceUnary, equationBaseDerivative, derivativeLinearMatrix,
      matrixPicardGraph, graphRealSealProvenance, localNamePkg⟩

end BEDC.Derived.ImplicitFunctionUp
