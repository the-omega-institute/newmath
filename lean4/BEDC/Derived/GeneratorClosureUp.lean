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

end BEDC.Derived.GeneratorClosureUp
