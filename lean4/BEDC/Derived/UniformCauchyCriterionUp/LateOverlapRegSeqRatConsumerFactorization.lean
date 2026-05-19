import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_late_overlap_regseqrat_consumer_factorization
    [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name regSeqRead
      realSealRead overlapRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont tail sealRow regSeqRead ->
        Cont regSeqRead transports realSealRead ->
          Cont realSealRead routes overlapRead ->
            PkgSig bundle overlapRead pkg ->
              UnaryHistory regSeqRead ∧ UnaryHistory realSealRead ∧ UnaryHistory overlapRead ∧
                Cont tail sealRow regSeqRead ∧ Cont regSeqRead transports realSealRead ∧
                  Cont realSealRead routes overlapRead ∧ PkgSig bundle name pkg ∧
                    PkgSig bundle overlapRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet tailSealRegSeq regSeqTransportsRealSeal realSealRoutesOverlap overlapPkg
  obtain ⟨_indexUnary, _windowsUnary, _modulusUnary, _toleranceUnary, tailUnary,
    sealRowUnary, transportsUnary, routesUnary, _provenanceUnary, _nameUnary,
    _indexWindowsModulus, _modulusToleranceTail, _tailSealTransports,
    _transportsRoutesProvenance, namePkg⟩ := packet
  have regSeqUnary : UnaryHistory regSeqRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealRegSeq
  have realSealUnary : UnaryHistory realSealRead :=
    unary_cont_closed regSeqUnary transportsUnary regSeqTransportsRealSeal
  have overlapUnary : UnaryHistory overlapRead :=
    unary_cont_closed realSealUnary routesUnary realSealRoutesOverlap
  exact
    ⟨regSeqUnary, realSealUnary, overlapUnary, tailSealRegSeq, regSeqTransportsRealSeal,
      realSealRoutesOverlap, namePkg, overlapPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
