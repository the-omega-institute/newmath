import BEDC.Derived.BishopRegularCauchyCompletionUp

namespace BEDC.Derived.BishopRegularCauchyCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BishopRegularCauchyCompletionScopedKernelRoute [AskSetup] [PackageSetup]
    {endpoint observations regularity tailModulus commonTail transport replay provenance
      localName toleranceRead windowRead regularRead sealRead scopeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BishopRegularCauchyCompletionCarrier endpoint observations regularity tailModulus
        commonTail transport replay provenance localName bundle pkg →
      Cont tailModulus commonTail toleranceRead →
        Cont toleranceRead observations windowRead →
          Cont windowRead regularity regularRead →
            Cont regularRead endpoint sealRead →
              Cont sealRead provenance scopeRead →
                PkgSig bundle scopeRead pkg →
                  UnaryHistory toleranceRead ∧ UnaryHistory windowRead ∧
                    UnaryHistory regularRead ∧ UnaryHistory sealRead ∧
                      UnaryHistory scopeRead ∧ Cont sealRead provenance scopeRead ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle scopeRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier tailCommon commonObservations observationsRegularity regularitySeal
    sealProvenance scopePkg
  obtain ⟨endpointUnary, observationsUnary, regularityUnary, tailModulusUnary,
    commonTailUnary, _transportUnary, _replayUnary, provenanceUnary, _localNameUnary,
    provenancePkg, _localNamePkg⟩ := carrier
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed tailModulusUnary commonTailUnary tailCommon
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed toleranceReadUnary observationsUnary commonObservations
  have regularReadUnary : UnaryHistory regularRead :=
    unary_cont_closed windowReadUnary regularityUnary observationsRegularity
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed regularReadUnary endpointUnary regularitySeal
  have scopeReadUnary : UnaryHistory scopeRead :=
    unary_cont_closed sealReadUnary provenanceUnary sealProvenance
  exact
    ⟨toleranceReadUnary, windowReadUnary, regularReadUnary, sealReadUnary,
      scopeReadUnary, sealProvenance, provenancePkg, scopePkg⟩

end BEDC.Derived.BishopRegularCauchyCompletionUp
