import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FiniteWitnessedRefutationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FiniteWitnessedRefutationCarrier [AskSetup] [PackageSetup]
    (regularity gap key witness decision transport route provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory regularity ∧ UnaryHistory gap ∧ UnaryHistory witness ∧
    UnaryHistory route ∧ Cont regularity gap key ∧ Cont key witness decision ∧
      Cont decision route transport ∧ PkgSig bundle provenance pkg ∧
        PkgSig bundle name pkg

theorem FiniteWitnessedRefutationCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {regularity gap key witness decision transport route provenance name publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteWitnessedRefutationCarrier regularity gap key witness decision transport route
        provenance name bundle pkg ->
      Cont decision route publicRead ->
        PkgSig bundle publicRead pkg ->
          SemanticNameCert
              (fun row : BHist =>
                FiniteWitnessedRefutationCarrier regularity gap key witness decision transport
                    route provenance name bundle pkg ∧ hsame row decision)
              (fun row : BHist => hsame row decision ∧ UnaryHistory publicRead)
              (fun row : BHist =>
                PkgSig bundle provenance pkg ∧ PkgSig bundle publicRead pkg ∧
                  hsame row decision)
              hsame ∧
            UnaryHistory key ∧ UnaryHistory decision ∧ UnaryHistory publicRead ∧
              Cont regularity gap key ∧ Cont key witness decision ∧
                Cont decision route publicRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle name pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier decisionRoutePublic publicPkg
  have carrierWitness :
      FiniteWitnessedRefutationCarrier regularity gap key witness decision transport route
        provenance name bundle pkg := carrier
  obtain ⟨regularityUnary, gapUnary, witnessUnary, routeUnary, regularityGapKey,
    keyWitnessDecision, _decisionRouteTransport, provenancePkg, namePkg⟩ := carrier
  have keyUnary : UnaryHistory key :=
    unary_cont_closed regularityUnary gapUnary regularityGapKey
  have decisionUnary : UnaryHistory decision :=
    unary_cont_closed keyUnary witnessUnary keyWitnessDecision
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed decisionUnary routeUnary decisionRoutePublic
  have certCore :
      NameCert
        (fun row : BHist =>
          FiniteWitnessedRefutationCarrier regularity gap key witness decision transport route
              provenance name bundle pkg ∧ hsame row decision)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro decision
        (And.intro carrierWitness (hsame_refl decision))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        exact And.intro source.left (hsame_trans (hsame_symm same) source.right)
    }
  have semantic :
      SemanticNameCert
          (fun row : BHist =>
            FiniteWitnessedRefutationCarrier regularity gap key witness decision transport route
                provenance name bundle pkg ∧ hsame row decision)
          (fun row : BHist => hsame row decision ∧ UnaryHistory publicRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle publicRead pkg ∧
              hsame row decision)
          hsame := by
    exact {
      core := certCore
      pattern_sound := by
        intro _row source
        exact And.intro source.right publicUnary
      ledger_sound := by
        intro _row source
        exact And.intro provenancePkg (And.intro publicPkg source.right)
    }
  exact
    And.intro semantic
      (And.intro keyUnary
        (And.intro decisionUnary
          (And.intro publicUnary
            (And.intro regularityGapKey
              (And.intro keyWitnessDecision
                  (And.intro decisionRoutePublic
                    (And.intro provenancePkg (And.intro namePkg publicPkg))))))))

theorem FiniteWitnessedRefutationLedgerExactness [AskSetup] [PackageSetup]
    {regularity gap key witness decision transport route provenance name publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteWitnessedRefutationCarrier regularity gap key witness decision transport route
        provenance name bundle pkg ->
      Cont decision route publicRead ->
        PkgSig bundle publicRead pkg ->
          UnaryHistory regularity ∧ UnaryHistory gap ∧ UnaryHistory key ∧
            UnaryHistory witness ∧ UnaryHistory decision ∧ UnaryHistory route ∧
              UnaryHistory publicRead ∧ Cont regularity gap key ∧
                Cont key witness decision ∧ Cont decision route publicRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg ∧
                    PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier decisionRoutePublic publicPkg
  obtain ⟨regularityUnary, gapUnary, witnessUnary, routeUnary, regularityGapKey,
    keyWitnessDecision, _decisionRouteTransport, provenancePkg, namePkg⟩ := carrier
  have keyUnary : UnaryHistory key :=
    unary_cont_closed regularityUnary gapUnary regularityGapKey
  have decisionUnary : UnaryHistory decision :=
    unary_cont_closed keyUnary witnessUnary keyWitnessDecision
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed decisionUnary routeUnary decisionRoutePublic
  exact
    ⟨regularityUnary, gapUnary, keyUnary, witnessUnary, decisionUnary, routeUnary,
      publicUnary, regularityGapKey, keyWitnessDecision, decisionRoutePublic,
      provenancePkg, namePkg, publicPkg⟩

theorem FiniteWitnessedRefutationCarrier_public_packet [AskSetup] [PackageSetup]
    {regularity gap key witness decision transport route provenance name publicRead
      consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteWitnessedRefutationCarrier regularity gap key witness decision transport route
        provenance name bundle pkg →
      Cont decision route publicRead →
        Cont publicRead route consumer →
          PkgSig bundle consumer pkg →
            UnaryHistory regularity ∧ UnaryHistory gap ∧ UnaryHistory key ∧
              UnaryHistory witness ∧ UnaryHistory decision ∧ UnaryHistory route ∧
                UnaryHistory publicRead ∧ UnaryHistory consumer ∧
                  Cont regularity gap key ∧ Cont key witness decision ∧
                    Cont decision route publicRead ∧ Cont publicRead route consumer ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg ∧
                        PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier decisionRoutePublic publicRouteConsumer consumerPkg
  obtain ⟨regularityUnary, gapUnary, witnessUnary, routeUnary, regularityGapKey,
    keyWitnessDecision, _decisionRouteTransport, provenancePkg, namePkg⟩ := carrier
  have keyUnary : UnaryHistory key :=
    unary_cont_closed regularityUnary gapUnary regularityGapKey
  have decisionUnary : UnaryHistory decision :=
    unary_cont_closed keyUnary witnessUnary keyWitnessDecision
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed decisionUnary routeUnary decisionRoutePublic
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed publicUnary routeUnary publicRouteConsumer
  exact
    ⟨regularityUnary, gapUnary, keyUnary, witnessUnary, decisionUnary, routeUnary,
      publicUnary, consumerUnary, regularityGapKey, keyWitnessDecision, decisionRoutePublic,
      publicRouteConsumer, provenancePkg, namePkg, consumerPkg⟩

theorem FiniteWitnessedRefutationCarrier_gap_boundary_crosslink [AskSetup] [PackageSetup]
    {regularity gap key witness decision transport route provenance name publicRead gapRefusal
      consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteWitnessedRefutationCarrier regularity gap key witness decision transport route
        provenance name bundle pkg →
      Cont decision route publicRead →
        Cont gap route gapRefusal →
          Cont gapRefusal decision consumer →
            PkgSig bundle publicRead pkg →
              PkgSig bundle consumer pkg →
                UnaryHistory gap ∧ UnaryHistory decision ∧ UnaryHistory publicRead ∧
                  UnaryHistory gapRefusal ∧ UnaryHistory consumer ∧
                    Cont decision route publicRead ∧ Cont gap route gapRefusal ∧
                      Cont gapRefusal decision consumer ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle publicRead pkg ∧ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier decisionRoutePublic gapRouteRefusal gapRefusalDecisionConsumer publicPkg
    consumerPkg
  obtain ⟨regularityUnary, gapUnary, witnessUnary, routeUnary, regularityGapKey,
    keyWitnessDecision, _decisionRouteTransport, provenancePkg, _namePkg⟩ := carrier
  have keyUnary : UnaryHistory key :=
    unary_cont_closed regularityUnary gapUnary regularityGapKey
  have decisionUnary : UnaryHistory decision :=
    unary_cont_closed keyUnary witnessUnary keyWitnessDecision
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed decisionUnary routeUnary decisionRoutePublic
  have gapRefusalUnary : UnaryHistory gapRefusal :=
    unary_cont_closed gapUnary routeUnary gapRouteRefusal
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed gapRefusalUnary decisionUnary gapRefusalDecisionConsumer
  exact
    ⟨gapUnary, decisionUnary, publicUnary, gapRefusalUnary, consumerUnary,
      decisionRoutePublic, gapRouteRefusal, gapRefusalDecisionConsumer, provenancePkg,
      publicPkg, consumerPkg⟩

theorem FiniteWitnessedRefutationCarrier_non_escape [AskSetup] [PackageSetup]
    {regularity gap key witness decision transport route provenance name publicRead
      consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteWitnessedRefutationCarrier regularity gap key witness decision transport route
        provenance name bundle pkg →
      Cont decision route publicRead →
        Cont publicRead route consumer →
          PkgSig bundle publicRead pkg →
            PkgSig bundle consumer pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    FiniteWitnessedRefutationCarrier regularity gap key witness decision
                        transport route provenance name bundle pkg ∧ hsame row decision)
                  (fun row : BHist =>
                    hsame row decision ∧ Cont decision route publicRead ∧
                      Cont publicRead route consumer)
                  (fun row : BHist =>
                    PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg ∧
                      PkgSig bundle publicRead pkg ∧ PkgSig bundle consumer pkg ∧
                        hsame row decision)
                  hsame ∧ UnaryHistory consumer ∧ Cont decision route publicRead ∧
                Cont publicRead route consumer := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier decisionRoutePublic publicRouteConsumer publicPkg consumerPkg
  have carrierWitness :
      FiniteWitnessedRefutationCarrier regularity gap key witness decision transport route
        provenance name bundle pkg := carrier
  obtain ⟨regularityUnary, gapUnary, witnessUnary, routeUnary, regularityGapKey,
    keyWitnessDecision, _decisionRouteTransport, provenancePkg, namePkg⟩ := carrier
  have keyUnary : UnaryHistory key :=
    unary_cont_closed regularityUnary gapUnary regularityGapKey
  have decisionUnary : UnaryHistory decision :=
    unary_cont_closed keyUnary witnessUnary keyWitnessDecision
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed decisionUnary routeUnary decisionRoutePublic
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed publicUnary routeUnary publicRouteConsumer
  have certCore :
      NameCert
        (fun row : BHist =>
          FiniteWitnessedRefutationCarrier regularity gap key witness decision transport route
              provenance name bundle pkg ∧ hsame row decision)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro decision
        (And.intro carrierWitness (hsame_refl decision))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        exact And.intro source.left (hsame_trans (hsame_symm same) source.right)
    }
  have semantic :
      SemanticNameCert
          (fun row : BHist =>
            FiniteWitnessedRefutationCarrier regularity gap key witness decision transport
                route provenance name bundle pkg ∧ hsame row decision)
          (fun row : BHist =>
            hsame row decision ∧ Cont decision route publicRead ∧
              Cont publicRead route consumer)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg ∧
              PkgSig bundle publicRead pkg ∧ PkgSig bundle consumer pkg ∧
                hsame row decision)
          hsame := by
    exact {
      core := certCore
      pattern_sound := by
        intro _row source
        exact And.intro source.right
          (And.intro decisionRoutePublic publicRouteConsumer)
      ledger_sound := by
        intro _row source
        exact And.intro provenancePkg
          (And.intro namePkg
            (And.intro publicPkg (And.intro consumerPkg source.right)))
    }
  exact And.intro semantic
    (And.intro consumerUnary (And.intro decisionRoutePublic publicRouteConsumer))

end BEDC.Derived.FiniteWitnessedRefutationUp
