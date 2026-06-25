import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyEquivalenceSetoidUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyEquivalenceSetoidCarrier [AskSetup] [PackageSetup]
    (s0 s1 r0 r1 dyadic test sealRow transport replay provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory s0 ∧ UnaryHistory s1 ∧ UnaryHistory r0 ∧ UnaryHistory r1 ∧
    UnaryHistory dyadic ∧ UnaryHistory test ∧ UnaryHistory sealRow ∧
      UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
        UnaryHistory name ∧ Cont s0 r0 transport ∧ Cont s1 r1 replay ∧
          Cont dyadic test sealRow ∧ PkgSig bundle provenance pkg ∧
            PkgSig bundle name pkg

theorem CauchyEquivalenceSetoidClassifierLaws [AskSetup] [PackageSetup]
    {s0 s1 r0 r1 dyadic test sealRow transport replay provenance name reflexive symmetric
      transitive : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyEquivalenceSetoidCarrier s0 s1 r0 r1 dyadic test sealRow transport replay
        provenance name bundle pkg ->
      Cont s0 r0 reflexive ->
        Cont s1 r1 symmetric ->
          Cont dyadic test transitive ->
            PkgSig bundle transitive pkg ->
              UnaryHistory s0 ∧ UnaryHistory s1 ∧ UnaryHistory r0 ∧ UnaryHistory r1 ∧
                UnaryHistory dyadic ∧ UnaryHistory test ∧ UnaryHistory reflexive ∧
                  UnaryHistory symmetric ∧ UnaryHistory transitive ∧ Cont s0 r0 reflexive ∧
                    Cont s1 r1 symmetric ∧ Cont dyadic test transitive ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle transitive pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier reflexiveRoute symmetricRoute transitiveRoute transitivePkg
  obtain ⟨s0Unary, s1Unary, r0Unary, r1Unary, dyadicUnary, testUnary, _sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, _leftTransport,
    _rightReplay, _dyadicSeal, provenancePkg, _namePkg⟩ := carrier
  have reflexiveUnary : UnaryHistory reflexive :=
    unary_cont_closed s0Unary r0Unary reflexiveRoute
  have symmetricUnary : UnaryHistory symmetric :=
    unary_cont_closed s1Unary r1Unary symmetricRoute
  have transitiveUnary : UnaryHistory transitive :=
    unary_cont_closed dyadicUnary testUnary transitiveRoute
  exact
    ⟨s0Unary, s1Unary, r0Unary, r1Unary, dyadicUnary, testUnary, reflexiveUnary,
      symmetricUnary, transitiveUnary, reflexiveRoute, symmetricRoute, transitiveRoute,
      provenancePkg, transitivePkg⟩

theorem CauchyEquivalenceSetoidNameCertSurface [AskSetup] [PackageSetup]
    {s0 s1 r0 r1 dyadic test sealRow transport replay provenance name sealRead equalityRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyEquivalenceSetoidCarrier s0 s1 r0 r1 dyadic test sealRow transport replay
        provenance name bundle pkg ->
      Cont test sealRow sealRead ->
        Cont sealRead replay equalityRead ->
          PkgSig bundle equalityRead pkg ->
            UnaryHistory s0 ∧ UnaryHistory s1 ∧ UnaryHistory r0 ∧ UnaryHistory r1 ∧
              UnaryHistory dyadic ∧ UnaryHistory test ∧ UnaryHistory sealRow ∧
                UnaryHistory sealRead ∧ UnaryHistory equalityRead ∧ Cont test sealRow sealRead ∧
                  Cont sealRead replay equalityRead ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle name pkg ∧ PkgSig bundle equalityRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier sealRoute equalityRoute equalityPkg
  obtain ⟨s0Unary, s1Unary, r0Unary, r1Unary, dyadicUnary, testUnary, sealUnary,
    _transportUnary, replayUnary, _provenanceUnary, _nameUnary, _leftTransport,
    _rightReplay, _dyadicSeal, provenancePkg, namePkg⟩ := carrier
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed testUnary sealUnary sealRoute
  have equalityReadUnary : UnaryHistory equalityRead :=
    unary_cont_closed sealReadUnary replayUnary equalityRoute
  exact
    ⟨s0Unary, s1Unary, r0Unary, r1Unary, dyadicUnary, testUnary, sealUnary,
      sealReadUnary, equalityReadUnary, sealRoute, equalityRoute, provenancePkg, namePkg,
      equalityPkg⟩

theorem CauchyEquivalenceSetoidTransport [AskSetup] [PackageSetup]
    {s0 s1 r0 r1 dyadic test sealRow transport replay provenance name transportedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyEquivalenceSetoidCarrier s0 s1 r0 r1 dyadic test sealRow transport replay
        provenance name bundle pkg ->
      hsame transport transportedRead ->
        UnaryHistory transportedRead ∧ PkgSig bundle provenance pkg ∧
          PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory hsame PkgSig
  intro carrier transportSame
  obtain ⟨_s0Unary, _s1Unary, _r0Unary, _r1Unary, _dyadicUnary, _testUnary,
    _sealUnary, transportUnary, _replayUnary, _provenanceUnary, _nameUnary,
    _leftTransport, _rightReplay, _dyadicSeal, provenancePkg, namePkg⟩ := carrier
  have transportedUnary : UnaryHistory transportedRead :=
    unary_transport transportUnary transportSame
  exact ⟨transportedUnary, provenancePkg, namePkg⟩

theorem CauchyEquivalenceSetoidRegularCauchyUniquenessHandoff [AskSetup] [PackageSetup]
    {s0 s1 r0 r1 dyadic test sealRow transport replay provenance name leftRead rightRead
      equalityRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyEquivalenceSetoidCarrier s0 s1 r0 r1 dyadic test sealRow transport replay
        provenance name bundle pkg ->
      Cont s0 r0 leftRead ->
        Cont s1 r1 rightRead ->
          Cont leftRead rightRead equalityRead ->
            PkgSig bundle equalityRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row equalityRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row s0 ∨ hsame row s1 ∨ hsame row r0 ∨ hsame row r1 ∨
                      hsame row dyadic ∨ hsame row test ∨ hsame row sealRow ∨
                        hsame row equalityRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont s0 r0 leftRead ∧ Cont s1 r1 rightRead ∧
                      Cont leftRead rightRead equalityRead ∧ PkgSig bundle equalityRead pkg)
                  hsame ∧
                UnaryHistory leftRead ∧ UnaryHistory rightRead ∧ UnaryHistory equalityRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig SemanticNameCert hsame
  intro carrier leftRoute rightRoute equalityRoute equalityPkg
  obtain ⟨s0Unary, s1Unary, r0Unary, r1Unary, _dyadicUnary, _testUnary, _sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, _leftTransport,
    _rightReplay, _dyadicSeal, _provenancePkg, _namePkg⟩ := carrier
  have leftReadUnary : UnaryHistory leftRead :=
    unary_cont_closed s0Unary r0Unary leftRoute
  have rightReadUnary : UnaryHistory rightRead :=
    unary_cont_closed s1Unary r1Unary rightRoute
  have equalityReadUnary : UnaryHistory equalityRead :=
    unary_cont_closed leftReadUnary rightReadUnary equalityRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row equalityRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row s0 ∨ hsame row s1 ∨ hsame row r0 ∨ hsame row r1 ∨
              hsame row dyadic ∨ hsame row test ∨ hsame row sealRow ∨
                hsame row equalityRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont s0 r0 leftRead ∧ Cont s1 r1 rightRead ∧
              Cont leftRead rightRead equalityRead ∧ PkgSig bundle equalityRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro equalityRead ⟨hsame_refl equalityRead, equalityReadUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left))))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, leftRoute, rightRoute, equalityRoute, equalityPkg⟩
  }
  exact ⟨cert, leftReadUnary, rightReadUnary, equalityReadUnary⟩

theorem CauchyEquivalenceSetoidRealEqualityConsumerRoute [AskSetup] [PackageSetup]
    {s0 s1 r0 r1 dyadic test sealRow transport replay provenance name sealRead equalityRead
      realEqualityRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyEquivalenceSetoidCarrier s0 s1 r0 r1 dyadic test sealRow transport replay
        provenance name bundle pkg →
      Cont test sealRow sealRead →
        Cont sealRead replay equalityRead →
          Cont equalityRead name realEqualityRead →
            PkgSig bundle equalityRead pkg →
              PkgSig bundle realEqualityRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row realEqualityRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row sealRead ∨ hsame row equalityRead ∨
                        hsame row realEqualityRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont test sealRow sealRead ∧
                        Cont sealRead replay equalityRead ∧
                          Cont equalityRead name realEqualityRead ∧
                            PkgSig bundle realEqualityRead pkg)
                    hsame ∧
                  UnaryHistory realEqualityRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame SemanticNameCert
  intro carrier sealRoute equalityRoute realEqualityRoute equalityPkg realEqualityPkg
  have surface :
      UnaryHistory s0 ∧ UnaryHistory s1 ∧ UnaryHistory r0 ∧ UnaryHistory r1 ∧
        UnaryHistory dyadic ∧ UnaryHistory test ∧ UnaryHistory sealRow ∧
          UnaryHistory sealRead ∧ UnaryHistory equalityRead ∧ Cont test sealRow sealRead ∧
            Cont sealRead replay equalityRead ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle name pkg ∧ PkgSig bundle equalityRead pkg :=
    CauchyEquivalenceSetoidNameCertSurface carrier sealRoute equalityRoute equalityPkg
  obtain ⟨_s0Unary, _s1Unary, _r0Unary, _r1Unary, _dyadicUnary, _testUnary,
    _sealUnary, _sealReadUnary, equalityReadUnary, _surfaceSealRoute,
    _surfaceEqualityRoute, _provenancePkg, _namePkg, _surfaceEqualityPkg⟩ := surface
  have realEqualityUnary : UnaryHistory realEqualityRead :=
    unary_cont_closed equalityReadUnary
      (by
        obtain ⟨_s0Unary, _s1Unary, _r0Unary, _r1Unary, _dyadicUnary, _testUnary,
          _sealUnary, _transportUnary, _replayUnary, _provenanceUnary, nameUnary,
          _leftTransport, _rightReplay, _dyadicSeal, _provenancePkg, _namePkg⟩ := carrier
        exact nameUnary)
      realEqualityRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realEqualityRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row sealRead ∨ hsame row equalityRead ∨ hsame row realEqualityRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont test sealRow sealRead ∧
              Cont sealRead replay equalityRead ∧ Cont equalityRead name realEqualityRead ∧
                PkgSig bundle realEqualityRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realEqualityRead
        ⟨hsame_refl realEqualityRead, realEqualityUnary⟩
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
      exact Or.inr (Or.inr source.left)
    ledger_sound := by
      intro _row source
      exact ⟨source.right, sealRoute, equalityRoute, realEqualityRoute, realEqualityPkg⟩
  }
  exact ⟨cert, realEqualityUnary⟩

theorem CauchyEquivalenceSetoidSeparatedCompletionForwardLink [AskSetup] [PackageSetup]
    {s0 s1 r0 r1 dyadic test sealRow transport replay provenance name sealRead
      completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyEquivalenceSetoidCarrier s0 s1 r0 r1 dyadic test sealRow transport replay
        provenance name bundle pkg →
      Cont test sealRow sealRead →
        Cont sealRead transport completionRead →
          PkgSig bundle completionRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row s0 ∨ hsame row s1 ∨ hsame row r0 ∨ hsame row r1 ∨
                    hsame row dyadic ∨ hsame row test ∨ hsame row sealRow ∨
                      hsame row transport ∨ hsame row replay ∨ hsame row provenance ∨
                        hsame row name ∨ hsame row completionRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont test sealRow sealRead ∧
                    Cont sealRead transport completionRead ∧
                      PkgSig bundle completionRead pkg)
                hsame ∧
              UnaryHistory sealRead ∧ UnaryHistory completionRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig SemanticNameCert hsame
  intro carrier sealRoute completionRoute completionPkg
  obtain ⟨_s0Unary, _s1Unary, _r0Unary, _r1Unary, _dyadicUnary, testUnary,
    sealUnary, transportUnary, _replayUnary, _provenanceUnary, _nameUnary,
    _leftTransport, _rightReplay, _dyadicSeal, _provenancePkg, _namePkg⟩ := carrier
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed testUnary sealUnary sealRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed sealReadUnary transportUnary completionRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row s0 ∨ hsame row s1 ∨ hsame row r0 ∨ hsame row r1 ∨
              hsame row dyadic ∨ hsame row test ∨ hsame row sealRow ∨
                hsame row transport ∨ hsame row replay ∨ hsame row provenance ∨
                  hsame row name ∨ hsame row completionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont test sealRow sealRead ∧
              Cont sealRead transport completionRead ∧ PkgSig bundle completionRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro completionRead
        ⟨hsame_refl completionRead, completionUnary⟩
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
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, sealRoute, completionRoute, completionPkg⟩
  }
  exact ⟨cert, sealReadUnary, completionUnary⟩

theorem CauchyEquivalenceSetoidRealSeparabilityBackwardLink [AskSetup] [PackageSetup]
    {s0 s1 r0 r1 dyadic test sealRow transport replay provenance name sealRead
      densityRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyEquivalenceSetoidCarrier s0 s1 r0 r1 dyadic test sealRow transport replay
        provenance name bundle pkg →
      Cont test sealRow sealRead →
        Cont sealRead name densityRead →
          PkgSig bundle densityRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row densityRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row s0 ∨ hsame row s1 ∨ hsame row r0 ∨ hsame row r1 ∨
                    hsame row dyadic ∨ hsame row test ∨ hsame row sealRow ∨
                      hsame row densityRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont test sealRow sealRead ∧
                    Cont sealRead name densityRead ∧ PkgSig bundle densityRead pkg)
                hsame ∧ UnaryHistory sealRead ∧ UnaryHistory densityRead ∧
              PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig SemanticNameCert hsame
  intro carrier sealRoute densityRoute densityPkg
  obtain ⟨_s0Unary, _s1Unary, _r0Unary, _r1Unary, _dyadicUnary, testUnary,
    sealUnary, _transportUnary, _replayUnary, _provenanceUnary, nameUnary,
    _leftTransport, _rightReplay, _dyadicSeal, provenancePkg, _namePkg⟩ := carrier
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed testUnary sealUnary sealRoute
  have densityUnary : UnaryHistory densityRead :=
    unary_cont_closed sealReadUnary nameUnary densityRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row densityRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row s0 ∨ hsame row s1 ∨ hsame row r0 ∨ hsame row r1 ∨
              hsame row dyadic ∨ hsame row test ∨ hsame row sealRow ∨
                hsame row densityRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont test sealRow sealRead ∧
              Cont sealRead name densityRead ∧ PkgSig bundle densityRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro densityRead ⟨hsame_refl densityRead, densityUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr sourceRow.left))))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, sealRoute, densityRoute, densityPkg⟩
  }
  exact ⟨cert, sealReadUnary, densityUnary, provenancePkg⟩

end BEDC.Derived.CauchyEquivalenceSetoidUp
