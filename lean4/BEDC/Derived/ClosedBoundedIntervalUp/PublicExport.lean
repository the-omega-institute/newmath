import BEDC.Derived.ClosedboundedintervalUp

namespace BEDC.Derived.ClosedboundedintervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedBoundedIntervalPacket_public_export [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback sealRow
        transport replay provenance localName exported bundle pkg ->
      Cont exported localName publicRead ->
        PkgSig bundle publicRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row lower ∨ hsame row upper ∨ hsame row order ∨
                  hsame row rational ∨ hsame row dyadic ∨ hsame row stream ∨
                    hsame row readback ∨ hsame row sealRow ∨ hsame row publicRead)
              (fun row : BHist =>
                hsame row publicRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle publicRead pkg)
              hsame ∧
            UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame UnaryHistory
  intro packet publicRoute publicPkg
  obtain ⟨_lowerUnary, _upperUnary, _orderUnary, _rationalUnary, _dyadicUnary,
    _streamUnary, _readbackUnary, _sealRowUnary, _transportUnary, _replayUnary,
    _provenanceUnary, localNameUnary, exportedUnary, _endpointRoute, _containmentRoute,
    _sealRoute, _transportRoute, _exportRoute, provenancePkg, _localNamePkg⟩ := packet
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed exportedUnary localNameUnary publicRoute
  have sourcePublic :
      (fun row : BHist => hsame row publicRead ∧ UnaryHistory row) publicRead := by
    exact ⟨hsame_refl publicRead, publicUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row lower ∨ hsame row upper ∨ hsame row order ∨ hsame row rational ∨
              hsame row dyadic ∨ hsame row stream ∨ hsame row readback ∨
                hsame row sealRow ∨ hsame row publicRead)
          (fun row : BHist =>
            hsame row publicRead ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead sourcePublic
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
                  (Or.inr (Or.inr (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, provenancePkg, publicPkg⟩
  }
  exact ⟨cert, publicUnary⟩

end BEDC.Derived.ClosedboundedintervalUp
