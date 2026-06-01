import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DyadicDensityRealEmbeddingComparisonUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DyadicDensityRealEmbeddingComparisonCarrier [AskSetup] [PackageSetup]
    (density embedding realEmbedding stream readback realSeal transport replay provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory
  UnaryHistory density ∧ UnaryHistory embedding ∧ UnaryHistory realEmbedding ∧
    UnaryHistory stream ∧ UnaryHistory readback ∧ UnaryHistory realSeal ∧
      UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
        UnaryHistory localName ∧ Cont density stream replay ∧
          Cont embedding stream replay ∧ Cont stream readback realSeal ∧
            PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg

theorem DyadicDensityRealEmbeddingComparisonCarrier_namecert_obligations
    [AskSetup] [PackageSetup]
    {density embedding realEmbedding stream readback realSeal transport replay provenance
      localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicDensityRealEmbeddingComparisonCarrier density embedding realEmbedding stream
        readback realSeal transport replay provenance localName bundle pkg →
      UnaryHistory density ∧ UnaryHistory embedding ∧ UnaryHistory realEmbedding ∧
        UnaryHistory stream ∧ UnaryHistory readback ∧ UnaryHistory realSeal ∧
          Cont density stream replay ∧ Cont embedding stream replay ∧
            Cont stream readback realSeal ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: DyadicDensityRealEmbeddingComparisonCarrier BHist Cont ProbeBundle Pkg
  intro carrier
  obtain ⟨densityUnary, embeddingUnary, realEmbeddingUnary, streamUnary, readbackUnary,
    realSealUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    densityReplay, embeddingReplay, sealReplay, provenancePkg, localNamePkg⟩ := carrier
  exact
    ⟨densityUnary, embeddingUnary, realEmbeddingUnary, streamUnary, readbackUnary,
      realSealUnary, densityReplay, embeddingReplay, sealReplay, provenancePkg,
      localNamePkg⟩

end BEDC.Derived.DyadicDensityRealEmbeddingComparisonUp
