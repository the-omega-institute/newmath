import BEDC.Derived.SequentialClosureUp.SequenceLimitHandoff

namespace BEDC.Derived.SequentialClosureUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SequentialClosureRegSeqRatLimitRoute [AskSetup] [PackageSetup]
    {T M S Q L U W R A H C P N limitRead windowRead regSeqRead realSealRead named :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SequentialClosureCarrier T M S Q L U W R A H C P N bundle pkg ->
      Cont L U limitRead ->
        Cont limitRead W windowRead ->
          Cont windowRead R regSeqRead ->
            Cont regSeqRead A realSealRead ->
              Cont realSealRead N named ->
                PkgSig bundle named pkg ->
                  UnaryHistory limitRead ∧ UnaryHistory windowRead ∧
                    UnaryHistory regSeqRead ∧ UnaryHistory realSealRead ∧
                      UnaryHistory named ∧ Cont L U limitRead ∧
                        Cont limitRead W windowRead ∧ Cont windowRead R regSeqRead ∧
                          Cont regSeqRead A realSealRead ∧
                            Cont realSealRead N named ∧ PkgSig bundle P pkg ∧
                              PkgSig bundle named pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier limitRoute windowRoute regSeqRoute realSealRoute namedRoute namedPkg
  obtain ⟨_topologyUnary, _metricUnary, _sourceUnary, _sequenceUnary, limitUnaryBase,
    requestUnary, windowUnaryBase, regSeqUnaryBase, realSealUnaryBase, _transportUnary,
    _continuationUnary, _provenanceUnary, nameUnary, provenancePkg⟩ := carrier
  have limitUnary : UnaryHistory limitRead :=
    unary_cont_closed limitUnaryBase requestUnary limitRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed limitUnary windowUnaryBase windowRoute
  have regSeqUnary : UnaryHistory regSeqRead :=
    unary_cont_closed windowUnary regSeqUnaryBase regSeqRoute
  have realSealUnary : UnaryHistory realSealRead :=
    unary_cont_closed regSeqUnary realSealUnaryBase realSealRoute
  have namedUnary : UnaryHistory named :=
    unary_cont_closed realSealUnary nameUnary namedRoute
  exact
    ⟨limitUnary, windowUnary, regSeqUnary, realSealUnary, namedUnary, limitRoute,
      windowRoute, regSeqRoute, realSealRoute, namedRoute, provenancePkg, namedPkg⟩

end BEDC.Derived.SequentialClosureUp
