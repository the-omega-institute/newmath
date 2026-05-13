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

end BEDC.Derived.GeneratorClosureUp
