import BEDC.Derived.MetaCICNormalizationFrontierUp.NameCertObligations

namespace BEDC.Derived.MetaCICNormalizationFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def MetaCICNormalizationFrontierVisibleObstructionPacket [AskSetup] [PackageSetup]
    (candidate normalEndpoint obstruction subjectSupport bhistSupport transport replay
      provenance localRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  UnaryHistory candidate ∧ UnaryHistory normalEndpoint ∧ UnaryHistory obstruction ∧
    UnaryHistory subjectSupport ∧ UnaryHistory bhistSupport ∧ UnaryHistory transport ∧
      UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory localRow ∧
        Cont candidate normalEndpoint obstruction ∧ Cont obstruction subjectSupport replay ∧
          PkgSig bundle provenance pkg

end BEDC.Derived.MetaCICNormalizationFrontierUp
