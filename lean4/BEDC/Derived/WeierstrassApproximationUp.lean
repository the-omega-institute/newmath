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

theorem WeierstrassApproximationPolynomialModulusLedger [AskSetup] [PackageSetup]
    {interval continuousMap error polynomial samples modulus uniformError transport replay provenance
      localName sampleRead polynomialRead errorRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    WeierstrassApproximationCarrier interval continuousMap error polynomial samples modulus
        uniformError transport replay provenance localName bundle pkg →
      Cont samples modulus sampleRead →
        Cont sampleRead polynomial polynomialRead →
          Cont polynomialRead uniformError errorRead →
            PkgSig bundle errorRead pkg →
              UnaryHistory samples ∧ UnaryHistory modulus ∧ UnaryHistory sampleRead ∧
                UnaryHistory polynomial ∧ UnaryHistory polynomialRead ∧
                  UnaryHistory uniformError ∧ UnaryHistory errorRead ∧
                    Cont samples modulus sampleRead ∧
                      Cont sampleRead polynomial polynomialRead ∧
                        Cont polynomialRead uniformError errorRead ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle errorRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier samplesModulusRead samplePolynomialRead polynomialErrorRead errorReadPkg
  obtain ⟨_intervalUnary, _continuousMapUnary, _errorUnary, polynomialUnary, samplesUnary,
    modulusUnary, uniformErrorUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, provenancePkg, _localNamePkg⟩ := carrier
  have sampleReadUnary : UnaryHistory sampleRead :=
    unary_cont_closed samplesUnary modulusUnary samplesModulusRead
  have polynomialReadUnary : UnaryHistory polynomialRead :=
    unary_cont_closed sampleReadUnary polynomialUnary samplePolynomialRead
  have errorReadUnary : UnaryHistory errorRead :=
    unary_cont_closed polynomialReadUnary uniformErrorUnary polynomialErrorRead
  exact
    ⟨samplesUnary, modulusUnary, sampleReadUnary, polynomialUnary, polynomialReadUnary,
      uniformErrorUnary, errorReadUnary, samplesModulusRead, samplePolynomialRead,
      polynomialErrorRead, provenancePkg, errorReadPkg⟩

end BEDC.Derived.WeierstrassApproximationUp
