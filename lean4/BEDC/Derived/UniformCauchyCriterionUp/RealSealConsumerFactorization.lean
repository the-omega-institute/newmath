import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_real_seal_consumer_factorization [AskSetup]
    [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name regseqRead
      realRead consumerRead completionRead hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index tail regseqRead ->
        Cont tail sealRow realRead ->
          Cont regseqRead realRead consumerRead ->
            Cont consumerRead provenance completionRead ->
              PkgSig bundle regseqRead pkg ->
                PkgSig bundle realRead pkg ->
                  PkgSig bundle consumerRead pkg ->
                    PkgSig bundle completionRead pkg ->
                      UnaryHistory regseqRead ∧ UnaryHistory realRead ∧
                        UnaryHistory consumerRead ∧ UnaryHistory completionRead ∧
                          Cont index windows modulus ∧ Cont modulus tolerance tail ∧
                            Cont index tail regseqRead ∧ Cont tail sealRow realRead ∧
                              Cont regseqRead realRead consumerRead ∧
                                Cont consumerRead provenance completionRead ∧
                                  PkgSig bundle name pkg ∧ PkgSig bundle completionRead pkg ∧
                                    (Cont completionRead (BHist.e0 hostTail) regseqRead ->
                                      False) ∧
                                      (Cont completionRead (BHist.e1 hostTail) realRead ->
                                        False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet indexTailRegseq tailSealReal regseqRealConsumer consumerProvenanceCompletion
    _regseqPkg _realPkg _consumerPkg completionPkg
  obtain ⟨indexUnary, _windowsUnary, _modulusUnary, _toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, provenanceUnary, _nameUnary, indexWindowsModulus,
    modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed indexUnary tailUnary indexTailRegseq
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealReal
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed regseqUnary realUnary regseqRealConsumer
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed consumerUnary provenanceUnary consumerProvenanceCompletion
  exact
    ⟨regseqUnary, realUnary, consumerUnary, completionUnary, indexWindowsModulus,
      modulusToleranceTail, indexTailRegseq, tailSealReal, regseqRealConsumer,
        consumerProvenanceCompletion, namePkg, completionPkg,
          (fun backToRegseq =>
            cont_triangle_cycle_right_zero_tail_absurd regseqRealConsumer
              consumerProvenanceCompletion backToRegseq),
          (fun backToReal =>
            let realRegseqConsumer : Cont realRead regseqRead consumerRead :=
              cont_result_hsame_transport
                (cont_intro (h := realRead) (k := regseqRead) rfl)
                (hsame_symm
                  (unary_cont_comm regseqUnary realUnary regseqRealConsumer
                    (cont_intro (h := realRead) (k := regseqRead) rfl)))
            cont_triangle_cycle_right_visible_tail_absurd realRegseqConsumer
              consumerProvenanceCompletion backToReal)⟩

end BEDC.Derived.UniformCauchyCriterionUp
