import BEDC.Derived.LocatedInfimumUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LocatedInfimumUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocatedInfimumClassifierStability [AskSetup] [PackageSetup]
    {family lower greatest window regseq realSeal transport route provenance name family' lower'
      greatest' window' regseq' realSeal' stableRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedInfimumCarrier family lower greatest window regseq realSeal transport route provenance
        name bundle pkg →
      hsame family family' →
        hsame lower lower' →
          hsame greatest greatest' →
            hsame window window' →
              hsame regseq regseq' →
                hsame realSeal realSeal' →
                  Cont lower' greatest' stableRead →
                    PkgSig bundle stableRead pkg →
                      UnaryHistory family' ∧ UnaryHistory lower' ∧
                        UnaryHistory greatest' ∧ UnaryHistory window' ∧
                          UnaryHistory regseq' ∧ UnaryHistory realSeal' ∧
                            UnaryHistory stableRead ∧ Cont lower' greatest' stableRead ∧
                              PkgSig bundle stableRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory hsame
  intro carrier familySame lowerSame greatestSame windowSame regseqSame realSealSame
    stableRoute stablePkg
  obtain ⟨familyUnary, lowerUnary, greatestUnary, windowUnary, regseqUnary, realSealUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _nameUnary, _regseqRealSealRoute,
    _provenancePkg, _namePkg⟩ := carrier
  have familyPrimeUnary : UnaryHistory family' :=
    unary_transport familyUnary familySame
  have lowerPrimeUnary : UnaryHistory lower' :=
    unary_transport lowerUnary lowerSame
  have greatestPrimeUnary : UnaryHistory greatest' :=
    unary_transport greatestUnary greatestSame
  have windowPrimeUnary : UnaryHistory window' :=
    unary_transport windowUnary windowSame
  have regseqPrimeUnary : UnaryHistory regseq' :=
    unary_transport regseqUnary regseqSame
  have realSealPrimeUnary : UnaryHistory realSeal' :=
    unary_transport realSealUnary realSealSame
  have stableUnary : UnaryHistory stableRead :=
    unary_cont_closed lowerPrimeUnary greatestPrimeUnary stableRoute
  exact
    ⟨familyPrimeUnary, lowerPrimeUnary, greatestPrimeUnary, windowPrimeUnary,
      regseqPrimeUnary, realSealPrimeUnary, stableUnary, stableRoute, stablePkg⟩

end BEDC.Derived.LocatedInfimumUp
