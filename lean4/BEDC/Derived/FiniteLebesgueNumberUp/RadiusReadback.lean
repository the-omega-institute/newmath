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

end BEDC.Derived.FiniteLebesgueNumberUp
