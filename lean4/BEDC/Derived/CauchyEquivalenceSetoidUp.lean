import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyEquivalenceSetoidUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyEquivalenceSetoidCarrier [AskSetup] [PackageSetup]
    (s0 s1 r0 r1 dyadic test sealRow transport replay provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory s0 ∧ UnaryHistory s1 ∧ UnaryHistory r0 ∧ UnaryHistory r1 ∧
    UnaryHistory dyadic ∧ UnaryHistory test ∧ UnaryHistory sealRow ∧
      UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
        UnaryHistory name ∧ Cont s0 r0 transport ∧ Cont s1 r1 replay ∧
          Cont dyadic test sealRow ∧ PkgSig bundle provenance pkg ∧
            PkgSig bundle name pkg

theorem CauchyEquivalenceSetoidClassifierLaws [AskSetup] [PackageSetup]
    {s0 s1 r0 r1 dyadic test sealRow transport replay provenance name reflexive symmetric
      transitive : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyEquivalenceSetoidCarrier s0 s1 r0 r1 dyadic test sealRow transport replay
        provenance name bundle pkg ->
      Cont s0 r0 reflexive ->
        Cont s1 r1 symmetric ->
          Cont dyadic test transitive ->
            PkgSig bundle transitive pkg ->
              UnaryHistory s0 ∧ UnaryHistory s1 ∧ UnaryHistory r0 ∧ UnaryHistory r1 ∧
                UnaryHistory dyadic ∧ UnaryHistory test ∧ UnaryHistory reflexive ∧
                  UnaryHistory symmetric ∧ UnaryHistory transitive ∧ Cont s0 r0 reflexive ∧
                    Cont s1 r1 symmetric ∧ Cont dyadic test transitive ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle transitive pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier reflexiveRoute symmetricRoute transitiveRoute transitivePkg
  obtain ⟨s0Unary, s1Unary, r0Unary, r1Unary, dyadicUnary, testUnary, _sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, _leftTransport,
    _rightReplay, _dyadicSeal, provenancePkg, _namePkg⟩ := carrier
  have reflexiveUnary : UnaryHistory reflexive :=
    unary_cont_closed s0Unary r0Unary reflexiveRoute
  have symmetricUnary : UnaryHistory symmetric :=
    unary_cont_closed s1Unary r1Unary symmetricRoute
  have transitiveUnary : UnaryHistory transitive :=
    unary_cont_closed dyadicUnary testUnary transitiveRoute
  exact
    ⟨s0Unary, s1Unary, r0Unary, r1Unary, dyadicUnary, testUnary, reflexiveUnary,
      symmetricUnary, transitiveUnary, reflexiveRoute, symmetricRoute, transitiveRoute,
      provenancePkg, transitivePkg⟩

theorem CauchyEquivalenceSetoidNameCertSurface [AskSetup] [PackageSetup]
    {s0 s1 r0 r1 dyadic test sealRow transport replay provenance name sealRead equalityRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyEquivalenceSetoidCarrier s0 s1 r0 r1 dyadic test sealRow transport replay
        provenance name bundle pkg ->
      Cont test sealRow sealRead ->
        Cont sealRead replay equalityRead ->
          PkgSig bundle equalityRead pkg ->
            UnaryHistory s0 ∧ UnaryHistory s1 ∧ UnaryHistory r0 ∧ UnaryHistory r1 ∧
              UnaryHistory dyadic ∧ UnaryHistory test ∧ UnaryHistory sealRow ∧
                UnaryHistory sealRead ∧ UnaryHistory equalityRead ∧ Cont test sealRow sealRead ∧
                  Cont sealRead replay equalityRead ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle name pkg ∧ PkgSig bundle equalityRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier sealRoute equalityRoute equalityPkg
  obtain ⟨s0Unary, s1Unary, r0Unary, r1Unary, dyadicUnary, testUnary, sealUnary,
    _transportUnary, replayUnary, _provenanceUnary, _nameUnary, _leftTransport,
    _rightReplay, _dyadicSeal, provenancePkg, namePkg⟩ := carrier
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed testUnary sealUnary sealRoute
  have equalityReadUnary : UnaryHistory equalityRead :=
    unary_cont_closed sealReadUnary replayUnary equalityRoute
  exact
    ⟨s0Unary, s1Unary, r0Unary, r1Unary, dyadicUnary, testUnary, sealUnary,
      sealReadUnary, equalityReadUnary, sealRoute, equalityRoute, provenancePkg, namePkg,
      equalityPkg⟩

end BEDC.Derived.CauchyEquivalenceSetoidUp
