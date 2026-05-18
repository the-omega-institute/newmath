import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_diagonal_uniqueness_four_face_terminal [AskSetup]
    [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name streamFace
      dyadicFace regseqFace realFace terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont windows tolerance streamFace ->
        Cont streamFace tail dyadicFace ->
          Cont dyadicFace sealRow regseqFace ->
            Cont regseqFace routes realFace ->
              Cont realFace provenance terminal ->
                PkgSig bundle terminal pkg ->
                  UnaryHistory streamFace ∧ UnaryHistory dyadicFace ∧
                    UnaryHistory regseqFace ∧ UnaryHistory realFace ∧
                      UnaryHistory terminal ∧ Cont windows tolerance streamFace ∧
                        Cont streamFace tail dyadicFace ∧
                          Cont dyadicFace sealRow regseqFace ∧
                            Cont regseqFace routes realFace ∧
                              Cont realFace provenance terminal ∧ PkgSig bundle name pkg ∧
                                PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet windowsToleranceStream streamTailDyadic dyadicSealRegseq regseqRoutesReal
    realProvenanceTerminal terminalPkg
  obtain ⟨_indexUnary, windowsUnary, _modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, routesUnary, provenanceUnary, _nameUnary, _indexWindowsModulus,
    _modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
      packet
  have streamUnary : UnaryHistory streamFace :=
    unary_cont_closed windowsUnary toleranceUnary windowsToleranceStream
  have dyadicUnary : UnaryHistory dyadicFace :=
    unary_cont_closed streamUnary tailUnary streamTailDyadic
  have regseqUnary : UnaryHistory regseqFace :=
    unary_cont_closed dyadicUnary sealRowUnary dyadicSealRegseq
  have realUnary : UnaryHistory realFace :=
    unary_cont_closed regseqUnary routesUnary regseqRoutesReal
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed realUnary provenanceUnary realProvenanceTerminal
  exact
    ⟨streamUnary, dyadicUnary, regseqUnary, realUnary, terminalUnary, windowsToleranceStream,
      streamTailDyadic, dyadicSealRegseq, regseqRoutesReal, realProvenanceTerminal, namePkg,
      terminalPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
