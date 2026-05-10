import BEDC.GroundCompiler.ImplementationInterface

namespace BEDC.GroundCompiler.ImplementationAdequacy

open BEDC.GroundCompiler.ImplementationInterface

def PublicRelationsSpecified (publicSurface : InterfaceDatum -> Prop) :
    Prop :=
  forall d, publicSurface d -> PublicFormalInterface d

def ImplementationAdequate
    (publicSurface : InterfaceDatum -> Prop)
    (soundForSpecs completeOnDomains bootstrapObligationsRecorded
      reportsAreOutputViews recognitionClaimsCertified
      compilerBoundaryHandled : Prop) : Prop :=
  PublicRelationsSpecified publicSurface /\
    soundForSpecs /\
    completeOnDomains /\
    NoHostLeakCondition publicSurface /\
    bootstrapObligationsRecorded /\
    reportsAreOutputViews /\
    recognitionClaimsCertified /\
    compilerBoundaryHandled

theorem implementation_adequacy
    {publicSurface : InterfaceDatum -> Prop}
    {soundForSpecs completeOnDomains bootstrapObligationsRecorded
      reportsAreOutputViews recognitionClaimsCertified
      compilerBoundaryHandled : Prop} :
    ImplementationAdequate publicSurface soundForSpecs completeOnDomains
      bootstrapObligationsRecorded reportsAreOutputViews
      recognitionClaimsCertified compilerBoundaryHandled <->
      PublicRelationsSpecified publicSurface /\
        soundForSpecs /\
        completeOnDomains /\
        NoHostLeakCondition publicSurface /\
        bootstrapObligationsRecorded /\
        reportsAreOutputViews /\
        recognitionClaimsCertified /\
        compilerBoundaryHandled := by
  constructor
  · intro h
    exact h
  · intro h
    exact h

theorem passing_tests_weaker_than_adequacy :
    ReferenceTestSuite /\
      Not (ImplementationAdequate ReferenceExecutablePublicSurface
        ReferenceTestSuite ReferenceTestSuite ReferenceTestSuite
        ReferenceTestSuite
        (FullNoHiddenInputCompilerInterface ReferenceExecutablePublicSurface)
        (FullNoHiddenInputCompilerInterface
          ReferenceExecutablePublicSurface)) := by
  constructor
  · exact reference_test_suite_holds
  · intro hAdequate
    have hSpecified :
        PublicRelationsSpecified ReferenceExecutablePublicSurface :=
      hAdequate.left
    have hFormal : PublicFormalInterface InterfaceDatum.motifReport :=
      hSpecified InterfaceDatum.motifReport
        ReferenceExecutablePublicSurface.motifReport
    cases hFormal

end BEDC.GroundCompiler.ImplementationAdequacy
