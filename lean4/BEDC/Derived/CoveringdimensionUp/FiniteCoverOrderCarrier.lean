import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CoveringDimensionFiniteCoverOrderCarrier [AskSetup] [PackageSetup]
    (compactMetric epsilonNet metricRead regSeqRead realSeal nerve orderTable transport replay
      provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory compactMetric ∧ UnaryHistory epsilonNet ∧ UnaryHistory metricRead ∧
    UnaryHistory regSeqRead ∧ UnaryHistory realSeal ∧ UnaryHistory nerve ∧
      UnaryHistory orderTable ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
        UnaryHistory provenance ∧ UnaryHistory localName ∧
          Cont compactMetric epsilonNet metricRead ∧ Cont metricRead regSeqRead realSeal ∧
            Cont epsilonNet nerve orderTable ∧ Cont transport replay provenance ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg

theorem CoveringDimensionFiniteCoverOrderAdmission [AskSetup] [PackageSetup]
    {compactMetric epsilonNet metricRead regSeqRead realSeal nerve orderTable transport replay
      provenance localName consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionFiniteCoverOrderCarrier compactMetric epsilonNet metricRead regSeqRead
        realSeal nerve orderTable transport replay provenance localName bundle pkg →
      Cont orderTable localName consumer →
        PkgSig bundle consumer pkg →
          SemanticNameCert
              (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row metricRead ∨
                  hsame row regSeqRead ∨ hsame row realSeal ∨ hsame row nerve ∨
                    hsame row orderTable ∨ hsame row consumer)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont compactMetric epsilonNet metricRead ∧
                  Cont metricRead regSeqRead realSeal ∧ Cont epsilonNet nerve orderTable ∧
                    Cont orderTable localName consumer ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle consumer pkg)
              hsame ∧
            UnaryHistory consumer := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame SemanticNameCert
  intro carrier consumerRoute consumerPkg
  obtain ⟨_compactUnary, _epsilonUnary, _metricReadUnary, _regSeqUnary, _realSealUnary,
    _nerveUnary, orderTableUnary, _transportUnary, _replayUnary, _provenanceUnary,
    localNameUnary, compactMetricRoute, metricRegSeqRoute, epsilonNerveRoute,
    _transportReplayRoute, provenancePkg, _localNamePkg⟩ := carrier
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed orderTableUnary localNameUnary consumerRoute
  have sourceConsumer :
      (fun row : BHist => hsame row consumer ∧ UnaryHistory row) consumer := by
    exact ⟨hsame_refl consumer, consumerUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row metricRead ∨
              hsame row regSeqRead ∨ hsame row realSeal ∨ hsame row nerve ∨
                hsame row orderTable ∨ hsame row consumer)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont compactMetric epsilonNet metricRead ∧
              Cont metricRead regSeqRead realSeal ∧ Cont epsilonNet nerve orderTable ∧
                Cont orderTable localName consumer ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle consumer pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro consumer sourceConsumer
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other sameRows source
          exact And.intro (hsame_trans (hsame_symm sameRows) source.left)
            (unary_transport source.right sameRows)
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, compactMetricRoute, metricRegSeqRoute, epsilonNerveRoute,
            consumerRoute, provenancePkg, consumerPkg⟩
    }
  exact ⟨cert, consumerUnary⟩

end BEDC.Derived.CoveringdimensionUp
