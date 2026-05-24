import BEDC.Derived.FiniteLebesgueNumberUp

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberRealSealRadiusReadback [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow dyadicRead windowRead
      realSealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg →
      Cont cover radius dyadicRead →
        Cont dyadicRead window windowRead →
          Cont windowRead route realSealRead →
            PkgSig bundle realSealRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row realSealRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row dyadicRead ∨ hsame row windowRead ∨
                      hsame row realSealRead)
                  (fun row : BHist =>
                    PkgSig bundle provenance pkg ∧ PkgSig bundle realSealRead pkg ∧
                      hsame row realSealRead)
                  hsame ∧
                UnaryHistory dyadicRead ∧ UnaryHistory windowRead ∧
                  UnaryHistory realSealRead ∧ Cont cover radius dyadicRead ∧
                    Cont dyadicRead window windowRead ∧ Cont windowRead route realSealRead ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle realSealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier coverRadiusDyadic dyadicWindowRead windowRouteSeal realSealPkg
  obtain ⟨coverUnary, windowUnary, radiusUnary, _meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, _nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed coverUnary radiusUnary coverRadiusDyadic
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed dyadicUnary windowUnary dyadicWindowRead
  have realSealUnary : UnaryHistory realSealRead :=
    unary_cont_closed windowReadUnary routeUnary windowRouteSeal
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row realSealRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row dyadicRead ∨ hsame row windowRead ∨ hsame row realSealRead)
        (fun row : BHist =>
          PkgSig bundle provenance pkg ∧ PkgSig bundle realSealRead pkg ∧
            hsame row realSealRead)
        hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro realSealRead ⟨hsame_refl realSealRead, realSealUnary⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact
            ⟨hsame_trans (hsame_symm same) source.left,
              unary_transport source.right same⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr source.left)
      ledger_sound := by
        intro _row source
        exact ⟨provenancePkg, realSealPkg, source.left⟩
    }
  exact
    ⟨cert, dyadicUnary, windowReadUnary, realSealUnary, coverRadiusDyadic,
      dyadicWindowRead, windowRouteSeal, provenancePkg, realSealPkg⟩

theorem FiniteLebesgueNumberOpenPhaseRadiusClassifierPullback [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow classifierRead compactRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg →
      Cont cover radius classifierRead →
        Cont classifierRead mesh compactRead →
          PkgSig bundle compactRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row compactRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row cover ∨ hsame row radius ∨ hsame row mesh ∨
                    hsame row compactRead)
                (fun row : BHist =>
                  PkgSig bundle provenance pkg ∧ PkgSig bundle compactRead pkg ∧
                    hsame row compactRead)
                hsame ∧
              UnaryHistory cover ∧ UnaryHistory radius ∧ UnaryHistory mesh ∧
                UnaryHistory classifierRead ∧ UnaryHistory compactRead ∧
                  Cont cover radius classifierRead ∧ Cont classifierRead mesh compactRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle compactRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier coverRadiusClassifier classifierMeshCompact compactPkg
  obtain ⟨coverUnary, _windowUnary, radiusUnary, meshUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed coverUnary radiusUnary coverRadiusClassifier
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed classifierUnary meshUnary classifierMeshCompact
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row compactRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row cover ∨ hsame row radius ∨ hsame row mesh ∨ hsame row compactRead)
        (fun row : BHist =>
          PkgSig bundle provenance pkg ∧ PkgSig bundle compactRead pkg ∧
            hsame row compactRead)
        hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro compactRead ⟨hsame_refl compactRead, compactUnary⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact
            ⟨hsame_trans (hsame_symm same) source.left,
              unary_transport source.right same⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr source.left))
      ledger_sound := by
        intro _row source
        exact ⟨provenancePkg, compactPkg, source.left⟩
    }
  exact
    ⟨cert, coverUnary, radiusUnary, meshUnary, classifierUnary, compactUnary,
      coverRadiusClassifier, classifierMeshCompact, provenancePkg, compactPkg⟩

theorem FiniteLebesgueNumberFourFaceRadiusReadback [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow dyadicRead streamRead
      regularRead realRead compactRead uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont cover radius dyadicRead ->
        Cont dyadicRead window streamRead ->
          Cont streamRead route regularRead ->
            Cont regularRead nameRow realRead ->
              Cont realRead mesh compactRead ->
                Cont compactRead nameRow uniformRead ->
                  PkgSig bundle uniformRead pkg ->
                    SemanticNameCert
                        (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row dyadicRead ∨ hsame row streamRead ∨
                            hsame row regularRead ∨ hsame row realRead ∨
                              hsame row uniformRead)
                        (fun row : BHist =>
                          PkgSig bundle uniformRead pkg ∧ hsame row uniformRead)
                        hsame ∧
                      UnaryHistory dyadicRead ∧ UnaryHistory streamRead ∧
                        UnaryHistory regularRead ∧ UnaryHistory realRead ∧
                          UnaryHistory compactRead ∧ UnaryHistory uniformRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier coverRadiusDyadic dyadicWindowStream streamRouteRegular
    regularNameReal realMeshCompact compactNameUniform uniformPkg
  obtain ⟨coverUnary, windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, _provenancePkg⟩ := carrier
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed coverUnary radiusUnary coverRadiusDyadic
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed dyadicUnary windowUnary dyadicWindowStream
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed streamUnary routeUnary streamRouteRegular
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed regularUnary nameRowUnary regularNameReal
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed realUnary meshUnary realMeshCompact
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed compactUnary nameRowUnary compactNameUniform
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row dyadicRead ∨ hsame row streamRead ∨ hsame row regularRead ∨
            hsame row realRead ∨ hsame row uniformRead)
        (fun row : BHist => PkgSig bundle uniformRead pkg ∧ hsame row uniformRead)
        hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro uniformRead ⟨hsame_refl uniformRead, uniformUnary⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact
            ⟨hsame_trans (hsame_symm same) source.left,
              unary_transport source.right same⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
      ledger_sound := by
        intro _row source
        exact ⟨uniformPkg, source.left⟩
    }
  exact
    ⟨cert, dyadicUnary, streamUnary, regularUnary, realUnary, compactUnary, uniformUnary⟩

theorem FiniteLebesgueNumberCompactUniformFourFaceReadiness [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow classifierRead compactRead
      compactNetRead uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg →
      Cont cover radius classifierRead →
        Cont classifierRead mesh compactRead →
          Cont compactRead route compactNetRead →
            Cont compactNetRead nameRow uniformRead →
              PkgSig bundle uniformRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row cover ∨ hsame row radius ∨ hsame row mesh ∨
                        hsame row uniformRead)
                    (fun row : BHist =>
                      PkgSig bundle provenance pkg ∧ PkgSig bundle uniformRead pkg ∧
                        hsame row uniformRead)
                    hsame ∧
                  UnaryHistory classifierRead ∧ UnaryHistory compactRead ∧
                    UnaryHistory compactNetRead ∧ UnaryHistory uniformRead ∧
                      Cont classifierRead mesh compactRead ∧
                        Cont compactRead route compactNetRead ∧
                          Cont compactNetRead nameRow uniformRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier coverRadiusClassifier classifierMeshCompact compactRouteCompactNet
    compactNetNameUniform uniformPkg
  obtain ⟨coverUnary, _windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed coverUnary radiusUnary coverRadiusClassifier
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed classifierUnary meshUnary classifierMeshCompact
  have compactNetUnary : UnaryHistory compactNetRead :=
    unary_cont_closed compactUnary routeUnary compactRouteCompactNet
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed compactNetUnary nameRowUnary compactNetNameUniform
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row cover ∨ hsame row radius ∨ hsame row mesh ∨ hsame row uniformRead)
        (fun row : BHist =>
          PkgSig bundle provenance pkg ∧ PkgSig bundle uniformRead pkg ∧
            hsame row uniformRead)
        hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro uniformRead ⟨hsame_refl uniformRead, uniformUnary⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact
            ⟨hsame_trans (hsame_symm same) source.left,
              unary_transport source.right same⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr source.left))
      ledger_sound := by
        intro _row source
        exact ⟨provenancePkg, uniformPkg, source.left⟩
    }
  exact
    ⟨cert, classifierUnary, compactUnary, compactNetUnary, uniformUnary,
      classifierMeshCompact, compactRouteCompactNet, compactNetNameUniform⟩

end BEDC.Derived.FiniteLebesgueNumberUp
