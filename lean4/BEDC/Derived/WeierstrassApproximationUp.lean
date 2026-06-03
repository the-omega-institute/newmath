import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.WeierstrassApproximationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def WeierstrassApproximationCarrier [AskSetup] [PackageSetup]
    (interval continuousMap error polynomial samples modulus uniformError transport replay provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory interval ∧ UnaryHistory continuousMap ∧ UnaryHistory error ∧
    UnaryHistory polynomial ∧ UnaryHistory samples ∧ UnaryHistory modulus ∧
      UnaryHistory uniformError ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
        UnaryHistory provenance ∧ UnaryHistory localName ∧ PkgSig bundle provenance pkg ∧
          PkgSig bundle localName pkg

theorem WeierstrassApproximationUniformLimitConsumer [AskSetup] [PackageSetup]
    {interval continuousMap error polynomial samples modulus uniformError transport replay provenance
      localName uniformLimitRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    WeierstrassApproximationCarrier interval continuousMap error polynomial samples modulus
        uniformError transport replay provenance localName bundle pkg →
      Cont uniformError provenance uniformLimitRead →
        PkgSig bundle uniformLimitRead pkg →
          UnaryHistory interval ∧ UnaryHistory polynomial ∧ UnaryHistory uniformError ∧
            Cont uniformError provenance uniformLimitRead ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle uniformLimitRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier uniformLimitRoute uniformLimitPkg
  obtain ⟨intervalUnary, _continuousMapUnary, _errorUnary, polynomialUnary, _samplesUnary,
    _modulusUnary, uniformErrorUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, provenancePkg, _localNamePkg⟩ := carrier
  exact
    ⟨intervalUnary, polynomialUnary, uniformErrorUnary, uniformLimitRoute, provenancePkg,
      uniformLimitPkg⟩

end BEDC.Derived.WeierstrassApproximationUp
