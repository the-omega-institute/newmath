import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

/-!
# MetricTriangleUniformEstimateUp finite carrier surface.
-/

namespace BEDC.Derived.MetricTriangleUniformEstimateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def MetricTriangleUniformEstimateCarrier [AskSetup] [PackageSetup]
    (sourceMetric targetMetric graph left right center sourceBoundLeft sourceBoundRight
      precision targetBoundLeft targetBoundRight targetTriangle transport route provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont PkgSig hsame
  UnaryHistory sourceMetric ∧ UnaryHistory targetMetric ∧ UnaryHistory graph ∧
    UnaryHistory left ∧ UnaryHistory right ∧ UnaryHistory center ∧
      UnaryHistory sourceBoundLeft ∧ UnaryHistory sourceBoundRight ∧
        UnaryHistory precision ∧ UnaryHistory targetBoundLeft ∧
          UnaryHistory targetBoundRight ∧ UnaryHistory targetTriangle ∧
            UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
              UnaryHistory localName ∧ Cont left center sourceBoundLeft ∧
                Cont right center sourceBoundRight ∧
                  Cont targetBoundLeft targetBoundRight targetTriangle ∧
                    Cont route provenance localName ∧ PkgSig bundle localName pkg ∧
                      hsame transport targetTriangle

end BEDC.Derived.MetricTriangleUniformEstimateUp
