import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BishopRegularCauchyCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BishopRegularCauchyCompletionCarrier [AskSetup] [PackageSetup]
    (endpoint observations regularity tailModulus commonTail transport replay provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory endpoint ∧ UnaryHistory observations ∧ UnaryHistory regularity ∧
    UnaryHistory tailModulus ∧ UnaryHistory commonTail ∧ UnaryHistory transport ∧
      UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
        PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg

theorem BishopRegularCauchyCompletionCarrier_common_tail_modulus_stability [AskSetup]
    [PackageSetup]
    {endpoint observations regularity tailModulus commonTail transport replay provenance
      localName toleranceRead windowRead regularRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BishopRegularCauchyCompletionCarrier endpoint observations regularity tailModulus
        commonTail transport replay provenance localName bundle pkg →
      Cont tailModulus commonTail toleranceRead →
        Cont toleranceRead observations windowRead →
          Cont windowRead regularity regularRead →
            Cont regularRead endpoint sealRead →
              PkgSig bundle sealRead pkg →
                UnaryHistory tailModulus ∧ UnaryHistory commonTail ∧
                  UnaryHistory toleranceRead ∧ UnaryHistory windowRead ∧
                    UnaryHistory regularRead ∧ UnaryHistory sealRead ∧
                      Cont tailModulus commonTail toleranceRead ∧
                        Cont toleranceRead observations windowRead ∧
                          Cont windowRead regularity regularRead ∧
                            Cont regularRead endpoint sealRead ∧
                              PkgSig bundle provenance pkg ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier tailCommon commonObservations observationsRegularity regularitySeal sealPkg
  obtain ⟨endpointUnary, observationsUnary, regularityUnary, tailModulusUnary,
    commonTailUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    provenancePkg, _localNamePkg⟩ := carrier
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed tailModulusUnary commonTailUnary tailCommon
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed toleranceReadUnary observationsUnary commonObservations
  have regularReadUnary : UnaryHistory regularRead :=
    unary_cont_closed windowReadUnary regularityUnary observationsRegularity
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed regularReadUnary endpointUnary regularitySeal
  exact
    ⟨tailModulusUnary, commonTailUnary, toleranceReadUnary, windowReadUnary,
      regularReadUnary, sealReadUnary, tailCommon, commonObservations, observationsRegularity,
      regularitySeal, provenancePkg, sealPkg⟩

theorem BishopRegularCauchyCompletionCarrier_seal_stability [AskSetup] [PackageSetup]
    {endpoint observations regularity tailModulus commonTail transport replay provenance
      localName toleranceRead windowRead regularRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BishopRegularCauchyCompletionCarrier endpoint observations regularity tailModulus
        commonTail transport replay provenance localName bundle pkg →
      Cont tailModulus commonTail toleranceRead →
        Cont toleranceRead observations windowRead →
          Cont windowRead regularity regularRead →
            Cont regularRead endpoint sealRead →
              PkgSig bundle sealRead pkg →
                UnaryHistory endpoint ∧ UnaryHistory observations ∧ UnaryHistory regularity ∧
                  UnaryHistory tailModulus ∧ UnaryHistory commonTail ∧ UnaryHistory sealRead ∧
                    Cont tailModulus commonTail toleranceRead ∧
                      Cont toleranceRead observations windowRead ∧
                        Cont windowRead regularity regularRead ∧
                          Cont regularRead endpoint sealRead ∧ PkgSig bundle provenance pkg ∧
                            PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier tailCommon commonObservations observationsRegularity regularitySeal sealPkg
  obtain ⟨endpointUnary, observationsUnary, regularityUnary, tailModulusUnary,
    commonTailUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    provenancePkg, _localNamePkg⟩ := carrier
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed tailModulusUnary commonTailUnary tailCommon
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed toleranceReadUnary observationsUnary commonObservations
  have regularReadUnary : UnaryHistory regularRead :=
    unary_cont_closed windowReadUnary regularityUnary observationsRegularity
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed regularReadUnary endpointUnary regularitySeal
  exact
    ⟨endpointUnary, observationsUnary, regularityUnary, tailModulusUnary, commonTailUnary,
      sealReadUnary, tailCommon, commonObservations, observationsRegularity, regularitySeal,
      provenancePkg, sealPkg⟩

theorem BishopRegularCauchyCompletionCarrier_tail_equivalence_quotient_free [AskSetup]
    [PackageSetup]
    {endpoint endpoint' observations observations' regularity regularity' tailModulus commonTail
      transport replay provenance localName transport' replay' provenance' localName'
      toleranceRead windowRead regularRead regularRead' sealRead sealRead' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg pkg' : Pkg} :
    BishopRegularCauchyCompletionCarrier endpoint observations regularity tailModulus
        commonTail transport replay provenance localName bundle pkg →
      BishopRegularCauchyCompletionCarrier endpoint' observations' regularity' tailModulus
          commonTail transport' replay' provenance' localName' bundle pkg' →
        Cont tailModulus commonTail toleranceRead →
          Cont toleranceRead observations windowRead →
            Cont windowRead regularity regularRead →
              Cont regularRead endpoint sealRead →
                Cont toleranceRead observations' windowRead →
                  Cont windowRead regularity' regularRead' →
                    Cont regularRead' endpoint' sealRead' →
                      PkgSig bundle sealRead pkg →
                        PkgSig bundle sealRead' pkg' →
                          UnaryHistory tailModulus ∧ UnaryHistory commonTail ∧
                            UnaryHistory toleranceRead ∧ UnaryHistory windowRead ∧
                              UnaryHistory regularRead ∧ UnaryHistory regularRead' ∧
                                UnaryHistory sealRead ∧ UnaryHistory sealRead' ∧
                                  PkgSig bundle provenance pkg ∧
                                    PkgSig bundle provenance' pkg' ∧
                                      PkgSig bundle sealRead pkg ∧
                                        PkgSig bundle sealRead' pkg' := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier carrier' tailCommon commonObservations observationsRegularity regularitySeal
    commonObservations' observationsRegularity' regularitySeal' sealPkg sealPkg'
  obtain ⟨endpointUnary, observationsUnary, regularityUnary, tailModulusUnary,
    commonTailUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    provenancePkg, _localNamePkg⟩ := carrier
  obtain ⟨endpointUnary', observationsUnary', regularityUnary', _tailModulusUnary',
    _commonTailUnary', _transportUnary', _replayUnary', _provenanceUnary', _localNameUnary',
    provenancePkg', _localNamePkg'⟩ := carrier'
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed tailModulusUnary commonTailUnary tailCommon
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed toleranceReadUnary observationsUnary commonObservations
  have regularReadUnary : UnaryHistory regularRead :=
    unary_cont_closed windowReadUnary regularityUnary observationsRegularity
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed regularReadUnary endpointUnary regularitySeal
  have regularReadUnary' : UnaryHistory regularRead' :=
    unary_cont_closed windowReadUnary regularityUnary' observationsRegularity'
  have sealReadUnary' : UnaryHistory sealRead' :=
    unary_cont_closed regularReadUnary' endpointUnary' regularitySeal'
  exact
    ⟨tailModulusUnary, commonTailUnary, toleranceReadUnary, windowReadUnary,
      regularReadUnary, regularReadUnary', sealReadUnary, sealReadUnary', provenancePkg,
      provenancePkg', sealPkg, sealPkg'⟩

theorem BishopRegularCauchyCompletionNonescapeExactness [AskSetup] [PackageSetup]
    {endpoint observations regularity tailModulus commonTail transport replay provenance localName
      read : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BishopRegularCauchyCompletionCarrier endpoint observations regularity tailModulus
        commonTail transport replay provenance localName bundle pkg →
      Cont replay provenance read →
        PkgSig bundle read pkg →
          UnaryHistory endpoint ∧ UnaryHistory observations ∧ UnaryHistory regularity ∧
            UnaryHistory tailModulus ∧ UnaryHistory commonTail ∧ UnaryHistory transport ∧
              UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
                Cont replay provenance read ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle read pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier replayRead readPkg
  obtain ⟨endpointUnary, observationsUnary, regularityUnary, tailModulusUnary,
    commonTailUnary, transportUnary, replayUnary, provenanceUnary, localNameUnary,
    provenancePkg, _localNamePkg⟩ := carrier
  exact
    ⟨endpointUnary, observationsUnary, regularityUnary, tailModulusUnary, commonTailUnary,
      transportUnary, replayUnary, provenanceUnary, localNameUnary, replayRead, provenancePkg,
      readPkg⟩

end BEDC.Derived.BishopRegularCauchyCompletionUp
