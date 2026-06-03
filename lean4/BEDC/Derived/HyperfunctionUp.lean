import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.HyperfunctionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HyperfunctionNamecertObligations [AskSetup] [PackageSetup]
    {T O B S Q A R D E K L M C P N boundaryRead sheafRead cohomologyRead complexRead
      distributionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory T →
      UnaryHistory O →
        UnaryHistory B →
          UnaryHistory S →
            UnaryHistory Q →
              UnaryHistory A →
                UnaryHistory D →
                  UnaryHistory E →
                    Cont T O boundaryRead →
                      Cont boundaryRead S sheafRead →
                        Cont sheafRead Q cohomologyRead →
                          Cont cohomologyRead A complexRead →
                            Cont complexRead D distributionRead →
                              PkgSig bundle M pkg →
                                PkgSig bundle N pkg →
                                  SemanticNameCert
                                      (fun row : BHist =>
                                        hsame row distributionRead ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row T ∨ hsame row O ∨ hsame row B ∨
                                          hsame row S ∨ hsame row Q ∨ hsame row A ∨
                                            hsame row R ∨ hsame row D ∨ hsame row E ∨
                                              hsame row K ∨ hsame row L ∨ hsame row M ∨
                                                hsame row C ∨ hsame row P ∨ hsame row N ∨
                                                  hsame row distributionRead)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧ Cont T O boundaryRead ∧
                                          Cont boundaryRead S sheafRead ∧
                                            Cont sheafRead Q cohomologyRead ∧
                                              Cont cohomologyRead A complexRead ∧
                                                Cont complexRead D distributionRead ∧
                                                  PkgSig bundle M pkg ∧ PkgSig bundle N pkg)
                                      hsame ∧
                                    UnaryHistory boundaryRead ∧ UnaryHistory sheafRead ∧
                                      UnaryHistory cohomologyRead ∧ UnaryHistory complexRead ∧
                                        UnaryHistory distributionRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro unaryT unaryO _unaryB unaryS unaryQ unaryA unaryD _unaryE boundaryRoute
    sheafRoute cohomologyRoute complexRoute distributionRoute packagePkg localNamePkg
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed unaryT unaryO boundaryRoute
  have sheafUnary : UnaryHistory sheafRead :=
    unary_cont_closed boundaryUnary unaryS sheafRoute
  have cohomologyUnary : UnaryHistory cohomologyRead :=
    unary_cont_closed sheafUnary unaryQ cohomologyRoute
  have complexUnary : UnaryHistory complexRead :=
    unary_cont_closed cohomologyUnary unaryA complexRoute
  have distributionUnary : UnaryHistory distributionRead :=
    unary_cont_closed complexUnary unaryD distributionRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row distributionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row O ∨ hsame row B ∨ hsame row S ∨ hsame row Q ∨
              hsame row A ∨ hsame row R ∨ hsame row D ∨ hsame row E ∨ hsame row K ∨
                hsame row L ∨ hsame row M ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                  hsame row distributionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont T O boundaryRead ∧ Cont boundaryRead S sheafRead ∧
              Cont sheafRead Q cohomologyRead ∧ Cont cohomologyRead A complexRead ∧
                Cont complexRead D distributionRead ∧ PkgSig bundle M pkg ∧
                  PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro distributionRead ⟨hsame_refl distributionRead, distributionUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr source.left))))))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, boundaryRoute, sheafRoute, cohomologyRoute, complexRoute,
          distributionRoute, packagePkg, localNamePkg⟩
  }
  exact
    ⟨cert, boundaryUnary, sheafUnary, cohomologyUnary, complexUnary, distributionUnary⟩

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
