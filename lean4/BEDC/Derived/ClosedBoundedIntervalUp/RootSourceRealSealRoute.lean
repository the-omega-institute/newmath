import BEDC.Derived.ClosedboundedintervalUp

namespace BEDC.Derived.ClosedboundedintervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedBoundedIntervalPacket_root_source_real_seal_route [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported rootSource realSealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback sealRow
        transport replay provenance localName exported bundle pkg ->
      Cont lower upper rootSource ->
        Cont rootSource sealRow realSealRead ->
          PkgSig bundle realSealRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row realSealRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row lower ∨ hsame row upper ∨ hsame row order ∨
                    hsame row rational ∨ hsame row dyadic ∨ hsame row stream ∨
                      hsame row readback ∨ hsame row sealRow ∨
                        Cont rootSource sealRow realSealRead)
                (fun row : BHist =>
                  PkgSig bundle provenance pkg ∧ PkgSig bundle realSealRead pkg ∧
                    hsame row realSealRead)
                hsame ∧
              UnaryHistory rootSource ∧ UnaryHistory realSealRead ∧ Cont lower upper rootSource ∧
                Cont rootSource sealRow realSealRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame UnaryHistory
  intro packet rootRoute realSealRoute realSealPkg
  obtain ⟨lowerUnary, upperUnary, _orderUnary, _rationalUnary, _dyadicUnary, _streamUnary,
    _readbackUnary, sealRowUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _exportedUnary, _endpointRoute, _containmentRoute, _sealRowRoute,
    _replayRoute, _nameRoute, provenancePkg, _localNamePkg⟩ := packet
  have rootUnary : UnaryHistory rootSource :=
    unary_cont_closed lowerUnary upperUnary rootRoute
  have realSealUnary : UnaryHistory realSealRead :=
    unary_cont_closed rootUnary sealRowUnary realSealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realSealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row lower ∨ hsame row upper ∨ hsame row order ∨
              hsame row rational ∨ hsame row dyadic ∨ hsame row stream ∨
                hsame row readback ∨ hsame row sealRow ∨
                  Cont rootSource sealRow realSealRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle realSealRead pkg ∧
              hsame row realSealRead)
          hsame := {
    core := {
      carrier_inhabited := ⟨realSealRead, hsame_refl realSealRead, realSealUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row _source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr (Or.inr (Or.inr (Or.inr realSealRoute)))))))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, realSealPkg, source.left⟩
  }
  exact ⟨cert, rootUnary, realSealUnary, rootRoute, realSealRoute, provenancePkg⟩

end BEDC.Derived.ClosedboundedintervalUp
