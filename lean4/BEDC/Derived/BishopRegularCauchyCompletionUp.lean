import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BishopRegularCauchyCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

theorem BishopRegularCauchyCompletionConsumerExactness [AskSetup] [PackageSetup]
    {endpoint observations regularity tailModulus commonTail transport replay provenance
      localName completionRead supportRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BishopRegularCauchyCompletionCarrier endpoint observations regularity tailModulus
        commonTail transport replay provenance localName bundle pkg →
      Cont commonTail transport completionRead →
        Cont completionRead replay supportRead →
          Cont supportRead localName publicRead →
            PkgSig bundle provenance pkg →
              PkgSig bundle localName pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row endpoint ∨ hsame row observations ∨ hsame row regularity ∨
                        hsame row tailModulus ∨ hsame row commonTail ∨
                          hsame row supportRead ∨ hsame row publicRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont commonTail transport completionRead ∧
                        Cont completionRead replay supportRead ∧
                          Cont supportRead localName publicRead ∧
                            PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
                    hsame ∧
                  UnaryHistory completionRead ∧ UnaryHistory supportRead ∧
                    UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BishopRegularCauchyCompletionCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier completionRoute supportRoute publicRoute provenancePkg localNamePkg
  obtain ⟨_endpointUnary, _observationsUnary, _regularityUnary, _tailModulusUnary,
    commonTailUnary, transportUnary, replayUnary, _provenanceUnary, localNameUnary,
    _carrierProvenancePkg, _carrierLocalNamePkg⟩ := carrier
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed commonTailUnary transportUnary completionRoute
  have supportUnary : UnaryHistory supportRead :=
    unary_cont_closed completionUnary replayUnary supportRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed supportUnary localNameUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row endpoint ∨ hsame row observations ∨ hsame row regularity ∨
              hsame row tailModulus ∨ hsame row commonTail ∨ hsame row supportRead ∨
                hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont commonTail transport completionRead ∧
              Cont completionRead replay supportRead ∧ Cont supportRead localName publicRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, completionRoute, supportRoute, publicRoute, provenancePkg,
          localNamePkg⟩
  }
  exact ⟨cert, completionUnary, supportUnary, publicUnary⟩

end BEDC.Derived.BishopRegularCauchyCompletionUp
