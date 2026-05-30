import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FastRegularCauchyEquivalenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FastRegularCauchyEquivalenceCarrier [AskSetup] [PackageSetup]
    (fast stream dyadic regular realSeal transport replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory PkgSig
  UnaryHistory fast ∧ UnaryHistory stream ∧ UnaryHistory dyadic ∧
    UnaryHistory regular ∧ UnaryHistory realSeal ∧ UnaryHistory transport ∧
      UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
        PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg

theorem FastRegularCauchyEquivalenceNameCert_obligations [AskSetup] [PackageSetup]
    {fast stream dyadic regular realSeal transport replay provenance localName fastWindow
      regularRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastRegularCauchyEquivalenceCarrier fast stream dyadic regular realSeal transport replay
        provenance localName bundle pkg →
      Cont fast stream fastWindow →
        Cont fastWindow dyadic regularRead →
          Cont regularRead regular sealRead →
            PkgSig bundle sealRead pkg →
              UnaryHistory fast ∧ UnaryHistory stream ∧ UnaryHistory dyadic ∧
                UnaryHistory regular ∧ UnaryHistory realSeal ∧ UnaryHistory fastWindow ∧
                  UnaryHistory regularRead ∧ UnaryHistory sealRead ∧
                    Cont fast stream fastWindow ∧ Cont fastWindow dyadic regularRead ∧
                      Cont regularRead regular sealRead ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle localName pkg ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier fastStream streamDyadic regularSeal sealPkg
  obtain ⟨fastUnary, streamUnary, dyadicUnary, regularUnary, realSealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary, provenancePkg,
    localNamePkg⟩ := carrier
  have fastWindowUnary : UnaryHistory fastWindow :=
    unary_cont_closed fastUnary streamUnary fastStream
  have regularReadUnary : UnaryHistory regularRead :=
    unary_cont_closed fastWindowUnary dyadicUnary streamDyadic
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed regularReadUnary regularUnary regularSeal
  exact
    ⟨fastUnary, streamUnary, dyadicUnary, regularUnary, realSealUnary, fastWindowUnary,
      regularReadUnary, sealReadUnary, fastStream, streamDyadic, regularSeal, provenancePkg,
      localNamePkg, sealPkg⟩

end BEDC.Derived.FastRegularCauchyEquivalenceUp
