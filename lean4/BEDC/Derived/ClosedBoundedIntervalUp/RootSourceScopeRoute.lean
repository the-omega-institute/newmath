import BEDC.Derived.ClosedboundedintervalUp

namespace BEDC.Derived.ClosedboundedintervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedBoundedIntervalPacket_root_source_scope_route [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported sourceRead sealRead routedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback sealRow
        transport replay provenance localName exported bundle pkg ->
      Cont lower upper sourceRead ->
        Cont sourceRead sealRow sealRead ->
          Cont sealRead provenance routedRead ->
            PkgSig bundle routedRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row routedRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row lower ∨ hsame row upper ∨ hsame row order ∨
                      hsame row rational ∨ hsame row dyadic ∨ hsame row stream ∨
                        hsame row readback ∨ hsame row sealRow ∨ hsame row routedRead)
                  (fun row : BHist =>
                    PkgSig bundle provenance pkg ∧ PkgSig bundle routedRead pkg ∧
                      hsame row routedRead)
                  hsame ∧
                UnaryHistory sourceRead ∧ UnaryHistory sealRead ∧ UnaryHistory routedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet sourceRoute sealReadRoute routedRoute routedPkg
  obtain ⟨lowerUnary, upperUnary, _orderUnary, _rationalUnary, _dyadicUnary, _streamUnary,
    _readbackUnary, sealRowUnary, _transportUnary, _replayUnary, provenanceUnary,
    _localNameUnary, _exportedUnary, _endpointRoute, _containmentRoute, _sealRowRoute,
    _replayRoute, _nameRoute, provenancePkg, _localNamePkg⟩ := packet
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed lowerUnary upperUnary sourceRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed sourceReadUnary sealRowUnary sealReadRoute
  have routedReadUnary : UnaryHistory routedRead :=
    unary_cont_closed sealReadUnary provenanceUnary routedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row routedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row lower ∨ hsame row upper ∨ hsame row order ∨
              hsame row rational ∨ hsame row dyadic ∨ hsame row stream ∨
                hsame row readback ∨ hsame row sealRow ∨ hsame row routedRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle routedRead pkg ∧
              hsame row routedRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro routedRead ⟨hsame_refl routedRead, routedReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, routedPkg, source.left⟩
  }
  exact ⟨cert, sourceReadUnary, sealReadUnary, routedReadUnary⟩

end BEDC.Derived.ClosedboundedintervalUp
