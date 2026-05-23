import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberSourceRadiusUnblock [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow sourceRead streamRead
      realRead compactRead uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont cover window sourceRead ->
        Cont sourceRead radius streamRead ->
          Cont streamRead mesh realRead ->
            Cont realRead route compactRead ->
              Cont compactRead nameRow uniformRead ->
                PkgSig bundle uniformRead pkg ->
                  UnaryHistory sourceRead ∧ UnaryHistory streamRead ∧
                    UnaryHistory realRead ∧ UnaryHistory compactRead ∧
                      UnaryHistory uniformRead ∧ Cont cover window sourceRead ∧
                        Cont sourceRead radius streamRead ∧
                          Cont streamRead mesh realRead ∧
                            Cont realRead route compactRead ∧
                              Cont compactRead nameRow uniformRead ∧
                                PkgSig bundle provenance pkg ∧
                                  PkgSig bundle uniformRead pkg ∧
                                    SemanticNameCert
                                      (fun row : BHist =>
                                        hsame row uniformRead ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row sourceRead ∨ hsame row streamRead ∨
                                          hsame row realRead ∨ hsame row compactRead ∨
                                            hsame row uniformRead)
                                      (fun row : BHist =>
                                        hsame row uniformRead ∧
                                          PkgSig bundle uniformRead pkg)
                                      hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier coverWindowSource sourceRadiusStream streamMeshReal realRouteCompact
    compactNameUniform uniformPkg
  obtain ⟨coverUnary, windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed coverUnary windowUnary coverWindowSource
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed sourceUnary radiusUnary sourceRadiusStream
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed streamUnary meshUnary streamMeshReal
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed realUnary routeUnary realRouteCompact
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed compactUnary nameRowUnary compactNameUniform
  have sourceUniform :
      (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row) uniformRead := by
    exact ⟨hsame_refl uniformRead, uniformUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row sourceRead ∨ hsame row streamRead ∨ hsame row realRead ∨
            hsame row compactRead ∨ hsame row uniformRead)
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
        exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
      ledger_sound := by
        intro _row source
        exact ⟨source.left, uniformPkg⟩
    }
  exact
    ⟨sourceUnary, streamUnary, realUnary, compactUnary, uniformUnary,
      coverWindowSource, sourceRadiusStream, streamMeshReal, realRouteCompact,
      compactNameUniform, provenancePkg, uniformPkg, cert⟩

theorem FiniteLebesgueNumberUniformContinuityHandoff [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow compactRead continuousRead
      uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont radius mesh compactRead ->
        Cont compactRead route continuousRead ->
          Cont continuousRead nameRow uniformRead ->
            PkgSig bundle uniformRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row compactRead ∨ hsame row continuousRead ∨
                      hsame row uniformRead)
                  (fun row : BHist => hsame row uniformRead ∧ PkgSig bundle uniformRead pkg)
                  hsame ∧
                UnaryHistory compactRead ∧ UnaryHistory continuousRead ∧
                  UnaryHistory uniformRead ∧ Cont radius mesh compactRead ∧
                    Cont compactRead route continuousRead ∧
                      Cont continuousRead nameRow uniformRead ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle uniformRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier radiusMeshCompact compactRouteContinuous continuousNameUniform uniformPkg
  obtain ⟨_coverUnary, _windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed radiusUnary meshUnary radiusMeshCompact
  have continuousUnary : UnaryHistory continuousRead :=
    unary_cont_closed compactUnary routeUnary compactRouteContinuous
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed continuousUnary nameRowUnary continuousNameUniform
  have sourceUniform :
      (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row) uniformRead := by
    exact ⟨hsame_refl uniformRead, uniformUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row compactRead ∨ hsame row continuousRead ∨ hsame row uniformRead)
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
        exact Or.inr (Or.inr source.left)
      ledger_sound := by
        intro _row source
        exact ⟨source.left, uniformPkg⟩
    }
  exact
    ⟨cert, compactUnary, continuousUnary, uniformUnary, radiusMeshCompact,
      compactRouteContinuous, continuousNameUniform, provenancePkg, uniformPkg⟩

end BEDC.Derived.FiniteLebesgueNumberUp
