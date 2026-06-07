import BEDC.Derived.FastCauchySubsequenceUp.NameCertObligations

namespace BEDC.Derived.FastCauchySubsequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FastCauchySubsequenceRegSeqRatCompletionHandoff [AskSetup] [PackageSetup]
    {S M Q F R W E H C P N modulusRead selectorRead fastRead regularRead regSeqRead
      realRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastCauchySubsequenceCarrier S M Q F R W E H C P N bundle pkg ->
      Cont S M modulusRead ->
        Cont modulusRead Q selectorRead ->
          Cont selectorRead F fastRead ->
            Cont fastRead R regularRead ->
              Cont regularRead W regSeqRead ->
                Cont regSeqRead E realRead ->
                  Cont realRead N namedRead ->
                    PkgSig bundle namedRead pkg ->
                      UnaryHistory modulusRead ∧ UnaryHistory selectorRead ∧
                        UnaryHistory fastRead ∧ UnaryHistory regularRead ∧
                          UnaryHistory regSeqRead ∧ UnaryHistory realRead ∧
                            UnaryHistory namedRead ∧ Cont fastRead R regularRead ∧
                              Cont regularRead W regSeqRead ∧ Cont regSeqRead E realRead ∧
                                Cont realRead N namedRead ∧ PkgSig bundle P pkg ∧
                                  PkgSig bundle namedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier modulusRoute selectorRoute fastRoute regularRoute regSeqRoute realRoute
    namedRoute namedPkg
  obtain ⟨sourceUnary, modulusUnaryBase, selectorUnaryBase, fastUnaryBase,
    regularUnaryBase, regSeqUnaryBase, realUnaryBase, _handoffUnary, _continuationUnary,
    _provenanceUnary, nameUnary, provenancePkg, _namePkg⟩ := carrier
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed sourceUnary modulusUnaryBase modulusRoute
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed modulusUnary selectorUnaryBase selectorRoute
  have fastUnary : UnaryHistory fastRead :=
    unary_cont_closed selectorUnary fastUnaryBase fastRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed fastUnary regularUnaryBase regularRoute
  have regSeqUnary : UnaryHistory regSeqRead :=
    unary_cont_closed regularUnary regSeqUnaryBase regSeqRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed regSeqUnary realUnaryBase realRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed realUnary nameUnary namedRoute
  exact
    ⟨modulusUnary, selectorUnary, fastUnary, regularUnary, regSeqUnary, realUnary,
      namedUnary, regularRoute, regSeqRoute, realRoute, namedRoute, provenancePkg,
      namedPkg⟩

end BEDC.Derived.FastCauchySubsequenceUp
