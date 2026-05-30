import BEDC.Derived.FastRegularCauchyEquivalenceUp.NameCertObligations

namespace BEDC.Derived.FastRegularCauchyEquivalenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FastRegularCauchyEquivalenceTwoWayRoute [AskSetup] [PackageSetup]
    {fast stream dyadic regular realSeal transport replay provenance localName fastWindow
      regularRead regularWindow fastRead fastSeal regularSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastRegularCauchyEquivalenceCarrier fast stream dyadic regular realSeal transport replay
        provenance localName bundle pkg →
      Cont fast stream fastWindow →
        Cont fastWindow dyadic regularRead →
          Cont regular stream regularWindow →
            Cont regularWindow dyadic fastRead →
              hsame regularRead regular →
                hsame fastRead fast →
                  Cont regularRead realSeal fastSeal →
                    Cont fastRead realSeal regularSeal →
                      PkgSig bundle fastSeal pkg →
                        PkgSig bundle regularSeal pkg →
                          UnaryHistory regularRead ∧ UnaryHistory fastRead ∧
                            UnaryHistory fastSeal ∧ UnaryHistory regularSeal ∧
                              hsame regularRead regular ∧ hsame fastRead fast ∧
                                Cont fastWindow dyadic regularRead ∧
                                  Cont regularWindow dyadic fastRead ∧
                                    PkgSig bundle fastSeal pkg ∧
                                      PkgSig bundle regularSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont hsame PkgSig
  intro carrier fastStream streamDyadic regularStream windowDyadic regularSame fastSame
    regularReadSeal fastReadSeal fastSealPkg regularSealPkg
  obtain ⟨fastUnary, streamUnary, dyadicUnary, regularUnary, realSealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary, _provenancePkg,
    _localNamePkg⟩ := carrier
  have fastWindowUnary : UnaryHistory fastWindow :=
    unary_cont_closed fastUnary streamUnary fastStream
  have regularReadUnary : UnaryHistory regularRead :=
    unary_cont_closed fastWindowUnary dyadicUnary streamDyadic
  have regularWindowUnary : UnaryHistory regularWindow :=
    unary_cont_closed regularUnary streamUnary regularStream
  have fastReadUnary : UnaryHistory fastRead :=
    unary_cont_closed regularWindowUnary dyadicUnary windowDyadic
  have fastSealUnary : UnaryHistory fastSeal :=
    unary_cont_closed regularReadUnary realSealUnary regularReadSeal
  have regularSealUnary : UnaryHistory regularSeal :=
    unary_cont_closed fastReadUnary realSealUnary fastReadSeal
  exact
    ⟨regularReadUnary, fastReadUnary, fastSealUnary, regularSealUnary, regularSame,
      fastSame, streamDyadic, windowDyadic, fastSealPkg, regularSealPkg⟩

end BEDC.Derived.FastRegularCauchyEquivalenceUp
