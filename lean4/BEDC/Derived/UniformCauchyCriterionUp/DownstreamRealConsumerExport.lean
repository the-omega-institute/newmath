import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_downstream_real_consumer_export [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name regseqRead
      realRead downstream hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index tail regseqRead ->
        Cont tail sealRow realRead ->
          Cont regseqRead realRead downstream ->
            PkgSig bundle regseqRead pkg ->
              PkgSig bundle realRead pkg ->
                PkgSig bundle downstream pkg ->
                  UnaryHistory regseqRead ∧ UnaryHistory realRead ∧
                    UnaryHistory downstream ∧ Cont index windows modulus ∧
                      Cont modulus tolerance tail ∧ Cont index tail regseqRead ∧
                        Cont tail sealRow realRead ∧ Cont regseqRead realRead downstream ∧
                          PkgSig bundle name pkg ∧ PkgSig bundle downstream pkg ∧
                            (Cont downstream (BHist.e0 hostTail) regseqRead -> False) ∧
                              (Cont downstream (BHist.e1 hostTail) realRead -> False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet indexTailRegseq tailSealReal regseqRealDownstream _regseqPkg _realPkg
    downstreamPkg
  obtain ⟨indexUnary, _windowsUnary, _modulusUnary, _toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, indexWindowsModulus,
    modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed indexUnary tailUnary indexTailRegseq
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealReal
  have downstreamUnary : UnaryHistory downstream :=
    unary_cont_closed regseqUnary realUnary regseqRealDownstream
  exact
    ⟨regseqUnary, realUnary, downstreamUnary, indexWindowsModulus, modulusToleranceTail,
      indexTailRegseq, tailSealReal, regseqRealDownstream, namePkg, downstreamPkg,
      (fun backToRegseq =>
        cont_mutual_extension_right_tail_absurd.left regseqRealDownstream backToRegseq),
      (fun backToReal =>
        let realRegseqDownstream : Cont realRead regseqRead downstream :=
          cont_result_hsame_transport
            (cont_intro (h := realRead) (k := regseqRead) rfl)
            (hsame_symm
              (unary_cont_comm regseqUnary realUnary regseqRealDownstream
                (cont_intro (h := realRead) (k := regseqRead) rfl)))
        cont_mutual_extension_right_tail_absurd.right realRegseqDownstream backToReal)⟩

end BEDC.Derived.UniformCauchyCriterionUp
