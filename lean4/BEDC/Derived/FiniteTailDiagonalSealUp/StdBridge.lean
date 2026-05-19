import BEDC.Derived.FiniteTailDiagonalSealUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.FiniteTailDiagonalSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteTailDiagonalSealUp_StdBridge [AskSetup] [PackageSetup]
    {precisionRow windowRow sourceRow witnessRow sealRow transportRow routeRow provenanceRow
      nameRow publicRead routeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteTailDiagonalSealCarrier precisionRow windowRow sourceRow witnessRow sealRow
        transportRow routeRow provenanceRow nameRow bundle pkg →
      Cont sourceRow witnessRow publicRead →
        Cont publicRead transportRow routeRead →
          PkgSig bundle publicRead pkg →
            PkgSig bundle routeRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row publicRead ∨ hsame row routeRead ∨ hsame row sealRow)
                  (fun row : BHist => hsame row routeRead ∧ PkgSig bundle routeRead pkg)
                  hsame ∧
                UnaryHistory routeRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier sourceWitnessPublic publicTransportRoute _publicPkg routePkg
  obtain ⟨_precisionUnary, _windowUnary, sourceUnary, witnessUnary, _sealUnary,
    transportUnary, _routeUnary, _provenanceUnary, _nameUnary, _precisionWindowSource,
    _sourceWitnessSeal, _sealTransportRoute, _provenancePkg, _namePkg⟩ := carrier
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed sourceUnary witnessUnary sourceWitnessPublic
  have routeUnary : UnaryHistory routeRead :=
    unary_cont_closed publicUnary transportUnary publicTransportRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row publicRead ∨ hsame row routeRead ∨ hsame row sealRow)
          (fun row : BHist => hsame row routeRead ∧ PkgSig bundle routeRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro routeRead ⟨hsame_refl routeRead, routeUnary⟩
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
      exact Or.inr (Or.inl source.left)
    ledger_sound := by
      intro _row source
      exact ⟨source.left, routePkg⟩
  }
  exact ⟨cert, routeUnary⟩

end BEDC.Derived.FiniteTailDiagonalSealUp
