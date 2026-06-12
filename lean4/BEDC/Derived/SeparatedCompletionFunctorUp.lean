import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SeparatedCompletionFunctorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def SeparatedCompletionFunctorCarrier [AskSetup] [PackageSetup]
    (sourceMetric targetMetric sourceMap sourceCompletion targetCompletion reflector
      metricCompletion stream regSeq realSeal transport replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory sourceMetric ∧ UnaryHistory targetMetric ∧ UnaryHistory sourceMap ∧
    UnaryHistory sourceCompletion ∧ UnaryHistory targetCompletion ∧
      UnaryHistory reflector ∧ UnaryHistory metricCompletion ∧ UnaryHistory stream ∧
        UnaryHistory regSeq ∧ UnaryHistory realSeal ∧ UnaryHistory transport ∧
          UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
            Cont sourceMetric targetMetric sourceMap ∧
              Cont sourceCompletion targetCompletion reflector ∧
                Cont reflector metricCompletion stream ∧ Cont stream regSeq realSeal ∧
                  Cont transport replay provenance ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle localName pkg

theorem SeparatedCompletionFunctorCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {sourceMetric targetMetric sourceMap sourceCompletion targetCompletion reflector
      metricCompletion stream regSeq realSeal transport replay provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SeparatedCompletionFunctorCarrier sourceMetric targetMetric sourceMap sourceCompletion
        targetCompletion reflector metricCompletion stream regSeq realSeal transport replay
        provenance localName bundle pkg →
      SemanticNameCert
          (fun row : BHist =>
            SeparatedCompletionFunctorCarrier sourceMetric targetMetric sourceMap
              sourceCompletion targetCompletion reflector metricCompletion stream regSeq realSeal
              transport replay provenance localName bundle pkg ∧ hsame row localName)
          (fun row : BHist => UnaryHistory row)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := by
  -- BEDC touchpoint anchor: SeparatedCompletionFunctorCarrier BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame SemanticNameCert
  intro carrier
  have carrierSource := carrier
  obtain ⟨_sourceMetricUnary, _targetMetricUnary, _sourceMapUnary, _sourceCompletionUnary,
    _targetCompletionUnary, _reflectorUnary, _metricCompletionUnary, _streamUnary,
    _regSeqUnary, _realSealUnary, _transportUnary, _replayUnary, _provenanceUnary,
    localNameUnary, _metricMapRoute, _separatedReflectorRoute, _reflectorStreamRoute,
    _streamRealRoute, _transportProvenanceRoute, provenancePkg, localNamePkg⟩ := carrier
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro localName ⟨carrierSource, hsame_refl localName⟩
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
        exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact unary_transport localNameUnary (hsame_symm source.right)
    ledger_sound := by
      intro _row source
      exact
        ⟨unary_transport localNameUnary (hsame_symm source.right), provenancePkg,
          localNamePkg⟩
  }

end BEDC.Derived.SeparatedCompletionFunctorUp
