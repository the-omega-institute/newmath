import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberCompactConsumerRadiusLedgerTotality [AskSetup]
    [PackageSetup]
    {cover window radius mesh transport route provenance nameRow streamRead regularRead
      realRead compactRead uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg →
      Cont window radius streamRead →
        Cont streamRead route regularRead →
          Cont regularRead nameRow realRead →
            Cont realRead mesh compactRead →
              Cont compactRead route uniformRead →
                PkgSig bundle uniformRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row streamRead ∨ hsame row regularRead ∨
                          hsame row realRead ∨ hsame row compactRead ∨
                            hsame row uniformRead)
                      (fun row : BHist => hsame row uniformRead ∧
                        PkgSig bundle uniformRead pkg)
                      hsame ∧
                    UnaryHistory streamRead ∧ UnaryHistory regularRead ∧
                      UnaryHistory realRead ∧ UnaryHistory compactRead ∧
                        UnaryHistory uniformRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier windowRadiusStream streamRouteRegular regularNameReal realMeshCompact
    compactRouteUniform uniformPkg
  obtain ⟨_coverUnary, windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, _provenancePkg⟩ := carrier
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed windowUnary radiusUnary windowRadiusStream
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed streamUnary routeUnary streamRouteRegular
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed regularUnary nameRowUnary regularNameReal
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed realUnary meshUnary realMeshCompact
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed compactUnary routeUnary compactRouteUniform
  have sourceUniform :
      (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row) uniformRead := by
    exact ⟨hsame_refl uniformRead, uniformUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row streamRead ∨ hsame row regularRead ∨
              hsame row realRead ∨ hsame row compactRead ∨ hsame row uniformRead)
          (fun row : BHist => hsame row uniformRead ∧ PkgSig bundle uniformRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro uniformRead sourceUniform
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
        exact ⟨source.left, uniformPkg⟩
    }
  exact ⟨cert, streamUnary, regularUnary, realUnary, compactUnary, uniformUnary⟩

end BEDC.Derived.FiniteLebesgueNumberUp
