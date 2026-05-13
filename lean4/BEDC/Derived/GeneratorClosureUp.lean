import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.GeneratorClosureUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def GeneratorClosurePacket [AskSetup] [PackageSetup]
    (generator constructors authorized classifier witnesses transport routes provenance name endpoint :
      BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory generator ∧ UnaryHistory constructors ∧ UnaryHistory authorized ∧
    UnaryHistory classifier ∧ UnaryHistory witnesses ∧ UnaryHistory transport ∧
      UnaryHistory provenance ∧ UnaryHistory name ∧ UnaryHistory endpoint ∧
        Cont generator constructors authorized ∧ Cont authorized classifier witnesses ∧
          Cont name endpoint routes ∧ PkgSig bundle endpoint pkg

theorem GeneratorClosurePacket_carrier_obligation [AskSetup] [PackageSetup]
    {generator constructors authorized classifier witnesses transport routes provenance name endpoint
      exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GeneratorClosurePacket generator constructors authorized classifier witnesses transport routes
        provenance name endpoint bundle pkg →
      hsame endpoint exported →
        Cont name exported routes →
          PkgSig bundle exported pkg →
            UnaryHistory generator ∧ UnaryHistory constructors ∧ UnaryHistory authorized ∧
              UnaryHistory witnesses ∧ UnaryHistory exported ∧
                Cont generator constructors authorized ∧ Cont authorized classifier witnesses ∧
                  Cont name exported routes ∧ PkgSig bundle endpoint pkg ∧
                    PkgSig bundle exported pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro packet sameEndpoint exportedRoute exportedPkg
  cases packet with
  | intro generatorUnary packet =>
  cases packet with
  | intro constructorsUnary packet =>
  cases packet with
  | intro authorizedUnary packet =>
  cases packet with
  | intro _classifierUnary packet =>
  cases packet with
  | intro witnessesUnary packet =>
  cases packet with
  | intro _transportUnary packet =>
  cases packet with
  | intro _provenanceUnary packet =>
  cases packet with
  | intro _nameUnary packet =>
  cases packet with
  | intro endpointUnary packet =>
  cases packet with
  | intro generatorRoute packet =>
  cases packet with
  | intro classifierRoute packet =>
  cases packet with
  | intro _endpointRoute endpointPkg =>
  cases sameEndpoint
  exact
    And.intro generatorUnary
      (And.intro constructorsUnary
        (And.intro authorizedUnary
          (And.intro witnessesUnary
            (And.intro endpointUnary
              (And.intro generatorRoute
                (And.intro classifierRoute
                  (And.intro exportedRoute
                    (And.intro endpointPkg exportedPkg))))))))

theorem GeneratorClosurePacket_classifier_obligation [AskSetup] [PackageSetup]
    {generator constructors authorized classifier witnesses transport routes provenance name endpoint
      generator' constructors' authorized' classifier' witnesses' transport' provenance' name'
      endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GeneratorClosurePacket generator constructors authorized classifier witnesses transport routes
        provenance name endpoint bundle pkg →
      hsame generator generator' →
        hsame constructors constructors' →
          hsame authorized authorized' →
            hsame classifier classifier' →
              hsame witnesses witnesses' →
                hsame transport transport' →
                  hsame provenance provenance' →
                    hsame name name' →
                      hsame endpoint endpoint' →
                        Cont generator' constructors' authorized' →
                          Cont authorized' classifier' witnesses' →
                            Cont name' endpoint' routes →
                              PkgSig bundle endpoint' pkg →
                                GeneratorClosurePacket generator' constructors' authorized'
                                    classifier' witnesses' transport' routes provenance' name'
                                    endpoint' bundle pkg ∧
                                  hsame endpoint endpoint' := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro packet sameGenerator sameConstructors sameAuthorized sameClassifier sameWitnesses
    sameTransport sameProvenance sameName sameEndpoint generatorRoute classifierRoute
    endpointRoute endpointPkg
  obtain ⟨generatorUnary, constructorsUnary, authorizedUnary, classifierUnary, witnessesUnary,
    transportUnary, provenanceUnary, nameUnary, endpointUnary, _oldGeneratorRoute,
    _oldClassifierRoute, _oldEndpointRoute, _oldEndpointPkg⟩ := packet
  have generatorUnary' : UnaryHistory generator' :=
    unary_transport generatorUnary sameGenerator
  have constructorsUnary' : UnaryHistory constructors' :=
    unary_transport constructorsUnary sameConstructors
  have authorizedUnary' : UnaryHistory authorized' :=
    unary_transport authorizedUnary sameAuthorized
  have classifierUnary' : UnaryHistory classifier' :=
    unary_transport classifierUnary sameClassifier
  have witnessesUnary' : UnaryHistory witnesses' :=
    unary_transport witnessesUnary sameWitnesses
  have transportUnary' : UnaryHistory transport' :=
    unary_transport transportUnary sameTransport
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  have nameUnary' : UnaryHistory name' :=
    unary_transport nameUnary sameName
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_transport endpointUnary sameEndpoint
  exact
    ⟨⟨generatorUnary',
      constructorsUnary',
      authorizedUnary',
      classifierUnary',
      witnessesUnary',
      transportUnary',
      provenanceUnary',
      nameUnary',
      endpointUnary',
      generatorRoute,
      classifierRoute,
      endpointRoute,
      endpointPkg⟩,
      sameEndpoint⟩

theorem GeneratorClosurePacket_ledger_obligation [AskSetup] [PackageSetup]
    {generator constructors authorized classifier witnesses transport routes provenance name endpoint
      exported rejected : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GeneratorClosurePacket generator constructors authorized classifier witnesses transport routes
        provenance name endpoint bundle pkg →
      hsame endpoint exported →
        Cont name exported routes →
          PkgSig bundle exported pkg →
            Cont constructors rejected routes →
              UnaryHistory generator ∧ UnaryHistory constructors ∧ UnaryHistory authorized ∧
                UnaryHistory witnesses ∧ UnaryHistory exported ∧
                  Cont generator constructors authorized ∧ Cont authorized classifier witnesses ∧
                    Cont name exported routes ∧ Cont constructors rejected routes ∧
                      PkgSig bundle endpoint pkg ∧ PkgSig bundle exported pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro packet sameEndpoint exportedRoute exportedPkg rejectedRoute
  obtain ⟨generatorUnary, constructorsUnary, authorizedUnary, _classifierUnary, witnessesUnary,
    _transportUnary, _provenanceUnary, _nameUnary, endpointUnary, generatorRoute,
    classifierRoute, _endpointRoute, endpointPkg⟩ := packet
  cases sameEndpoint
  exact
    ⟨generatorUnary,
      constructorsUnary,
      authorizedUnary,
      witnessesUnary,
      endpointUnary,
      generatorRoute,
      classifierRoute,
      exportedRoute,
      rejectedRoute,
      endpointPkg,
      exportedPkg⟩

theorem GeneratorClosurePacket_gap_boundary_absorbs_unwitnessed_route [AskSetup]
    [PackageSetup]
    {generator constructors authorized classifier witnesses transport routes provenance name endpoint
      exported rejected : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GeneratorClosurePacket generator constructors authorized classifier witnesses transport routes
        provenance name endpoint bundle pkg →
      hsame endpoint exported →
        Cont name exported routes →
          PkgSig bundle exported pkg →
            Cont constructors rejected routes →
              UnaryHistory constructors ∧ UnaryHistory rejected ∧
                Cont constructors rejected routes ∧ Cont name exported routes ∧
                  PkgSig bundle exported pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro packet sameEndpoint exportedRoute exportedPkg rejectedRoute
  obtain ⟨_generatorUnary, constructorsUnary, _authorizedUnary, _classifierUnary,
    _witnessesUnary, _transportUnary, _provenanceUnary, nameUnary, endpointUnary,
    _generatorRoute, _classifierRoute, _endpointRoute, _endpointPkg⟩ := packet
  cases sameEndpoint
  have routesUnary : UnaryHistory routes :=
    unary_cont_closed nameUnary endpointUnary exportedRoute
  have rejectedUnary : UnaryHistory rejected :=
    unary_cont_right_factor rejectedRoute routesUnary
  exact ⟨constructorsUnary, rejectedUnary, rejectedRoute, exportedRoute, exportedPkg⟩

theorem GeneratorClosurePacket_fixedpoint_acceptance_route [AskSetup] [PackageSetup]
    {generator constructors authorized classifier witnesses transport routes provenance name endpoint
      exported fixed : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GeneratorClosurePacket generator constructors authorized classifier witnesses transport routes
        provenance name endpoint bundle pkg →
      hsame endpoint exported →
        Cont name exported routes →
          PkgSig bundle exported pkg →
            Cont exported witnesses fixed →
              PkgSig bundle fixed pkg →
                UnaryHistory constructors ∧ UnaryHistory witnesses ∧ UnaryHistory exported ∧
                  UnaryHistory fixed ∧ Cont name exported routes ∧
                    Cont exported witnesses fixed ∧ PkgSig bundle endpoint pkg ∧
                      PkgSig bundle exported pkg ∧ PkgSig bundle fixed pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro packet sameEndpoint exportedRoute exportedPkg fixedRoute fixedPkg
  obtain ⟨_generatorUnary, constructorsUnary, _authorizedUnary, _classifierUnary,
    witnessesUnary, _transportUnary, _provenanceUnary, _nameUnary, endpointUnary,
    _generatorRoute, _classifierRoute, _endpointRoute, endpointPkg⟩ := packet
  have exportedUnary : UnaryHistory exported :=
    unary_transport endpointUnary sameEndpoint
  have fixedUnary : UnaryHistory fixed :=
    unary_cont_closed exportedUnary witnessesUnary fixedRoute
  exact
    ⟨constructorsUnary,
      witnessesUnary,
      exportedUnary,
      fixedUnary,
      exportedRoute,
      fixedRoute,
      endpointPkg,
      exportedPkg,
      fixedPkg⟩

end BEDC.Derived.GeneratorClosureUp
