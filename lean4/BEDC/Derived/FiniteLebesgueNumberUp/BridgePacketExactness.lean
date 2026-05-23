import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberBridgePacketExactness [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow dyadicRead radiusRead meshRead
      bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg →
      Cont cover window dyadicRead →
        Cont dyadicRead radius radiusRead →
          Cont radius mesh meshRead →
            Cont mesh route bridgeRead →
              PkgSig bundle bridgeRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row dyadicRead ∨ hsame row radiusRead ∨ hsame row meshRead ∨
                        hsame row bridgeRead)
                    (fun row : BHist =>
                      PkgSig bundle provenance pkg ∧ PkgSig bundle bridgeRead pkg ∧
                        hsame row bridgeRead)
                    hsame ∧
                  UnaryHistory dyadicRead ∧ UnaryHistory radiusRead ∧ UnaryHistory meshRead ∧
                    UnaryHistory bridgeRead ∧ Cont cover window dyadicRead ∧
                      Cont dyadicRead radius radiusRead ∧ Cont radius mesh meshRead ∧
                        Cont mesh route bridgeRead ∧ PkgSig bundle provenance pkg ∧
                          PkgSig bundle bridgeRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg SemanticNameCert hsame
  intro carrier coverWindowDyadic dyadicRadiusRead radiusMeshRead meshRouteBridge bridgePkg
  obtain ⟨coverUnary, windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, _nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed coverUnary windowUnary coverWindowDyadic
  have radiusReadUnary : UnaryHistory radiusRead :=
    unary_cont_closed dyadicUnary radiusUnary dyadicRadiusRead
  have meshReadUnary : UnaryHistory meshRead :=
    unary_cont_closed radiusUnary meshUnary radiusMeshRead
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed meshUnary routeUnary meshRouteBridge
  have sourceBridge :
      (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row) bridgeRead := by
    exact ⟨hsame_refl bridgeRead, bridgeUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row dyadicRead ∨ hsame row radiusRead ∨ hsame row meshRead ∨
            hsame row bridgeRead)
        (fun row : BHist =>
          PkgSig bundle provenance pkg ∧ PkgSig bundle bridgeRead pkg ∧
            hsame row bridgeRead)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro bridgeRead sourceBridge
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
        exact ⟨provenancePkg, bridgePkg, source.left⟩
    }
  exact
    ⟨cert, dyadicUnary, radiusReadUnary, meshReadUnary, bridgeUnary, coverWindowDyadic,
      dyadicRadiusRead, radiusMeshRead, meshRouteBridge, provenancePkg, bridgePkg⟩

theorem FiniteLebesgueNumberCompactUniformBridgeSoundness [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow compactRead compactNetRead
      uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg →
      Cont cover window compactRead →
        Cont compactRead radius compactNetRead →
          Cont compactNetRead route uniformRead →
            PkgSig bundle uniformRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row cover ∨ hsame row window ∨ hsame row radius ∨ hsame row mesh ∨
                      hsame row route ∨ hsame row uniformRead)
                  (fun row : BHist =>
                    hsame row uniformRead ∧ PkgSig bundle uniformRead pkg)
                  hsame ∧
                UnaryHistory compactRead ∧ UnaryHistory compactNetRead ∧
                  UnaryHistory uniformRead := by
  -- BEDC touchpoint anchor: BHist Cont Pkg SemanticNameCert hsame
  intro carrier coverWindowCompact compactRadiusNet compactNetRouteUniform uniformPkg
  obtain ⟨coverUnary, windowUnary, radiusUnary, _meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, _nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, _provenancePkg⟩ := carrier
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed coverUnary windowUnary coverWindowCompact
  have compactNetUnary : UnaryHistory compactNetRead :=
    unary_cont_closed compactUnary radiusUnary compactRadiusNet
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed compactNetUnary routeUnary compactNetRouteUniform
  have sourceUniform :
      (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row) uniformRead := by
    exact ⟨hsame_refl uniformRead, uniformUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row cover ∨ hsame row window ∨ hsame row radius ∨ hsame row mesh ∨
              hsame row route ∨ hsame row uniformRead)
          (fun row : BHist => hsame row uniformRead ∧ PkgSig bundle uniformRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro uniformRead sourceUniform
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
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
      ledger_sound := by
        intro _row source
        exact ⟨source.left, uniformPkg⟩
    }
  exact ⟨cert, compactUnary, compactNetUnary, uniformUnary⟩

theorem FiniteLebesgueNumberBridgeNonescape [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow dyadicRead radiusRead meshRead
      bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg →
      Cont cover window dyadicRead →
        Cont dyadicRead radius radiusRead →
          Cont radius mesh meshRead →
            Cont mesh route bridgeRead →
              PkgSig bundle bridgeRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row cover ∨ hsame row window ∨ hsame row radius ∨
                        hsame row mesh ∨ hsame row route ∨ hsame row bridgeRead)
                    (fun row : BHist =>
                      hsame row bridgeRead ∧ PkgSig bundle bridgeRead pkg)
                    hsame ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle bridgeRead pkg ∧
                    hsame bridgeRead bridgeRead := by
  -- BEDC touchpoint anchor: BHist Cont Pkg SemanticNameCert hsame
  intro carrier coverWindowDyadic dyadicRadiusRead radiusMeshRead meshRouteBridge bridgePkg
  obtain ⟨coverUnary, windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, _nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed coverUnary windowUnary coverWindowDyadic
  have radiusReadUnary : UnaryHistory radiusRead :=
    unary_cont_closed dyadicUnary radiusUnary dyadicRadiusRead
  have _meshReadUnary : UnaryHistory meshRead :=
    unary_cont_closed radiusUnary meshUnary radiusMeshRead
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed meshUnary routeUnary meshRouteBridge
  have sourceBridge :
      (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row) bridgeRead := by
    exact ⟨hsame_refl bridgeRead, bridgeUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row cover ∨ hsame row window ∨ hsame row radius ∨ hsame row mesh ∨
              hsame row route ∨ hsame row bridgeRead)
          (fun row : BHist => hsame row bridgeRead ∧ PkgSig bundle bridgeRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro bridgeRead sourceBridge
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
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
      ledger_sound := by
        intro _row source
        exact ⟨source.left, bridgePkg⟩
    }
  exact ⟨cert, provenancePkg, bridgePkg, hsame_refl bridgeRead⟩

end BEDC.Derived.FiniteLebesgueNumberUp
