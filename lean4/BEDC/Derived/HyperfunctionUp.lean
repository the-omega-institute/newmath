import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.HyperfunctionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def HyperfunctionCarrier [AskSetup] [PackageSetup]
    (topology openDomain boundary sheaf cohomology complex realRead distribution exactness
      transport replay provenance compatibility consumer localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory
  UnaryHistory topology ∧ UnaryHistory openDomain ∧ UnaryHistory boundary ∧
    UnaryHistory sheaf ∧ UnaryHistory cohomology ∧ UnaryHistory complex ∧
      UnaryHistory realRead ∧ UnaryHistory distribution ∧ UnaryHistory exactness ∧
        UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
          UnaryHistory compatibility ∧ UnaryHistory consumer ∧ UnaryHistory localName ∧
            Cont topology openDomain boundary ∧ Cont sheaf cohomology exactness ∧
              Cont complex realRead compatibility ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle consumer pkg ∧ PkgSig bundle localName pkg

theorem HyperfunctionCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {topology openDomain boundary sheaf cohomology complex realRead distribution exactness
      transport replay provenance compatibility consumer localName boundaryRead sheafRead
      cohomologyRead exactnessRead handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HyperfunctionCarrier topology openDomain boundary sheaf cohomology complex realRead
        distribution exactness transport replay provenance compatibility consumer localName
        bundle pkg →
      Cont topology openDomain boundaryRead →
        Cont boundaryRead sheaf sheafRead →
          Cont sheaf cohomology cohomologyRead →
            Cont cohomology exactness exactnessRead →
              Cont exactness distribution handoffRead →
                PkgSig bundle handoffRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row boundaryRead ∨ hsame row sheafRead ∨
                          hsame row cohomologyRead ∨ hsame row exactnessRead ∨
                            hsame row handoffRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ PkgSig bundle handoffRead pkg ∧
                          PkgSig bundle provenance pkg)
                      hsame ∧
                    UnaryHistory boundaryRead ∧ UnaryHistory sheafRead ∧
                      UnaryHistory cohomologyRead ∧ UnaryHistory exactnessRead ∧
                        UnaryHistory handoffRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier topologyOpenBoundary boundarySheafRead sheafCohomologyRead
    cohomologyExactnessRead exactnessDistributionHandoff handoffPkg
  obtain ⟨topologyUnary, openDomainUnary, _boundaryUnary, sheafUnary, cohomologyUnary,
    _complexUnary, _realReadUnary, distributionUnary, exactnessUnary, _transportUnary,
    _replayUnary, _provenanceUnary, _compatibilityUnary, _consumerUnary, _localNameUnary,
    _topologyOpenBoundary, _sheafCohomologyExactness, _complexRealCompatibility,
    provenancePkg, _consumerPkg, _localNamePkg⟩ := carrier
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed topologyUnary openDomainUnary topologyOpenBoundary
  have sheafReadUnary : UnaryHistory sheafRead :=
    unary_cont_closed boundaryReadUnary sheafUnary boundarySheafRead
  have cohomologyReadUnary : UnaryHistory cohomologyRead :=
    unary_cont_closed sheafUnary cohomologyUnary sheafCohomologyRead
  have exactnessReadUnary : UnaryHistory exactnessRead :=
    unary_cont_closed cohomologyUnary exactnessUnary cohomologyExactnessRead
  have handoffReadUnary : UnaryHistory handoffRead :=
    unary_cont_closed exactnessUnary distributionUnary exactnessDistributionHandoff
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row boundaryRead ∨ hsame row sheafRead ∨ hsame row cohomologyRead ∨
              hsame row exactnessRead ∨ hsame row handoffRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle handoffRead pkg ∧
              PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro handoffRead
        ⟨hsame_refl handoffRead, handoffReadUnary⟩
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
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, handoffPkg, provenancePkg⟩
  }
  exact
    ⟨cert, boundaryReadUnary, sheafReadUnary, cohomologyReadUnary, exactnessReadUnary,
      handoffReadUnary⟩

theorem HyperfunctionCarrier_sheaf_cohomology_handoff [AskSetup] [PackageSetup]
    {topology openDomain boundary sheaf cohomology complex realRead distribution exactness
      transport replay provenance compatibility consumer localName boundaryRead sheafRead
      cohomologyRead complexRead realBoundaryRead distributionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HyperfunctionCarrier topology openDomain boundary sheaf cohomology complex realRead
        distribution exactness transport replay provenance compatibility consumer localName
        bundle pkg →
      Cont topology openDomain boundaryRead →
        Cont boundaryRead sheaf sheafRead →
          Cont sheaf cohomology cohomologyRead →
            Cont cohomology complex complexRead →
              Cont complex realRead realBoundaryRead →
                Cont realBoundaryRead distribution distributionRead →
                  PkgSig bundle distributionRead pkg →
                    UnaryHistory boundaryRead ∧ UnaryHistory sheafRead ∧
                      UnaryHistory cohomologyRead ∧ UnaryHistory complexRead ∧
                        UnaryHistory realBoundaryRead ∧ UnaryHistory distributionRead ∧
                          Cont topology openDomain boundaryRead ∧
                            Cont boundaryRead sheaf sheafRead ∧
                              Cont sheaf cohomology cohomologyRead ∧
                                Cont cohomology complex complexRead ∧
                                  Cont complex realRead realBoundaryRead ∧
                                    Cont realBoundaryRead distribution distributionRead ∧
                                      PkgSig bundle provenance pkg ∧
                                        PkgSig bundle distributionRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier topologyOpenBoundary boundarySheafRead sheafCohomologyRead
    cohomologyComplexRead complexRealBoundary realDistributionRead distributionPkg
  obtain ⟨topologyUnary, openDomainUnary, _boundaryUnary, sheafUnary, cohomologyUnary,
    complexUnary, realReadUnary, distributionUnary, _exactnessUnary, _transportUnary,
    _replayUnary, _provenanceUnary, _compatibilityUnary, _consumerUnary, _localNameUnary,
    _topologyOpenBoundary, _sheafCohomologyExactness, _complexRealCompatibility,
    provenancePkg, _consumerPkg, _localNamePkg⟩ := carrier
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed topologyUnary openDomainUnary topologyOpenBoundary
  have sheafReadUnary : UnaryHistory sheafRead :=
    unary_cont_closed boundaryReadUnary sheafUnary boundarySheafRead
  have cohomologyReadUnary : UnaryHistory cohomologyRead :=
    unary_cont_closed sheafUnary cohomologyUnary sheafCohomologyRead
  have complexReadUnary : UnaryHistory complexRead :=
    unary_cont_closed cohomologyUnary complexUnary cohomologyComplexRead
  have realBoundaryReadUnary : UnaryHistory realBoundaryRead :=
    unary_cont_closed complexUnary realReadUnary complexRealBoundary
  have distributionReadUnary : UnaryHistory distributionRead :=
    unary_cont_closed realBoundaryReadUnary distributionUnary realDistributionRead
  exact
    ⟨boundaryReadUnary, sheafReadUnary, cohomologyReadUnary, complexReadUnary,
      realBoundaryReadUnary, distributionReadUnary, topologyOpenBoundary,
        boundarySheafRead, sheafCohomologyRead, cohomologyComplexRead,
          complexRealBoundary, realDistributionRead, provenancePkg, distributionPkg⟩

end BEDC.Derived.HyperfunctionUp
