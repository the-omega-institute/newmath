import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_real_seal_frontier_lock
    [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name streamRead
      regseqRead limitRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont windows modulus streamRead ->
        Cont streamRead tolerance regseqRead ->
          Cont tail sealRow limitRead ->
            Cont limitRead routes completionRead ->
              PkgSig bundle streamRead pkg ->
                PkgSig bundle regseqRead pkg ->
                  PkgSig bundle limitRead pkg ->
                    PkgSig bundle completionRead pkg ->
                      UnaryHistory index ∧ UnaryHistory windows ∧ UnaryHistory modulus ∧
                        UnaryHistory tolerance ∧ UnaryHistory tail ∧ UnaryHistory sealRow ∧
                          UnaryHistory streamRead ∧ UnaryHistory regseqRead ∧
                            UnaryHistory limitRead ∧ UnaryHistory completionRead ∧
                              Cont index windows modulus ∧ Cont windows modulus streamRead ∧
                                Cont streamRead tolerance regseqRead ∧
                                  Cont modulus tolerance tail ∧ Cont tail sealRow limitRead ∧
                                    Cont limitRead routes completionRead ∧
                                      PkgSig bundle name pkg ∧
                                        PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet windowsModulusStream streamToleranceRegseq tailSealLimit
    limitRoutesCompletion _streamPkg _regseqPkg _limitPkg completionPkg
  obtain ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, routesUnary, _provenanceUnary, _nameUnary, indexWindowsModulus,
    modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed windowsUnary modulusUnary windowsModulusStream
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed streamUnary toleranceUnary streamToleranceRegseq
  have limitUnary : UnaryHistory limitRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealLimit
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed limitUnary routesUnary limitRoutesCompletion
  exact
    ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
      streamUnary, regseqUnary, limitUnary, completionUnary, indexWindowsModulus,
      windowsModulusStream, streamToleranceRegseq, modulusToleranceTail, tailSealLimit,
      limitRoutesCompletion, namePkg, completionPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
