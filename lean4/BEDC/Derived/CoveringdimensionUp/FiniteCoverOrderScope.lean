import BEDC.Derived.CoveringdimensionUp.FiniteCoverOrderCarrier

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionFiniteCoverOrderScope [AskSetup] [PackageSetup]
    {compactMetric epsilonNet metricRead regSeqRead realSeal nerve orderTable transport replay
      provenance localName orderRead scopedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionFiniteCoverOrderCarrier compactMetric epsilonNet metricRead regSeqRead
        realSeal nerve orderTable transport replay provenance localName bundle pkg →
      Cont nerve orderTable orderRead →
        Cont orderRead localName scopedRead →
          PkgSig bundle scopedRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row metricRead ∨
                    hsame row regSeqRead ∨ hsame row realSeal ∨ hsame row nerve ∨
                      hsame row orderTable ∨ hsame row orderRead ∨ hsame row scopedRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont compactMetric epsilonNet metricRead ∧
                    Cont metricRead regSeqRead realSeal ∧ Cont epsilonNet nerve orderTable ∧
                      Cont nerve orderTable orderRead ∧
                        Cont orderRead localName scopedRead ∧
                          PkgSig bundle scopedRead pkg)
                hsame ∧
              UnaryHistory orderRead ∧ UnaryHistory scopedRead := by
  -- BEDC touchpoint anchor: CoveringDimensionFiniteCoverOrderCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier orderRoute scopedRoute scopedPkg
  obtain ⟨_compactUnary, _epsilonUnary, _metricUnary, _regSeqUnary, _realSealUnary,
    nerveUnary, orderTableUnary, _transportUnary, _replayUnary, _provenanceUnary,
    localNameUnary, compactMetricRoute, metricRegSeqRoute, epsilonNerveRoute,
    _transportReplayRoute, _provenancePkg, _localNamePkg⟩ := carrier
  have orderReadUnary : UnaryHistory orderRead :=
    unary_cont_closed nerveUnary orderTableUnary orderRoute
  have scopedReadUnary : UnaryHistory scopedRead :=
    unary_cont_closed orderReadUnary localNameUnary scopedRoute
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro scopedRead ⟨hsame_refl scopedRead, scopedReadUnary⟩
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
          exact
            ⟨hsame_trans (hsame_symm sameRows) source.left,
              unary_transport source.right sameRows⟩
      }
      pattern_sound := by
        intro _row source
        exact
          Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr source.left)))))))
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, compactMetricRoute, metricRegSeqRoute, epsilonNerveRoute,
            orderRoute, scopedRoute, scopedPkg⟩
    }
  · exact ⟨orderReadUnary, scopedReadUnary⟩

end BEDC.Derived.CoveringdimensionUp
