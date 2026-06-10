import BEDC.Derived.ClosedboundedintervalUp

namespace BEDC.Derived.ClosedboundedintervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedBoundedIntervalPublicBridgeBoundary [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported publicRead finiteCoverRead locatedCoverRead modulusRead
      compactRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback sealRow
        transport replay provenance localName exported bundle pkg →
      Cont exported localName publicRead →
        Cont publicRead dyadic finiteCoverRead →
          Cont finiteCoverRead stream locatedCoverRead →
            Cont locatedCoverRead sealRow modulusRead →
              Cont modulusRead readback compactRead →
                PkgSig bundle compactRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row compactRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row publicRead ∨ hsame row finiteCoverRead ∨
                          hsame row locatedCoverRead ∨ hsame row modulusRead ∨
                            hsame row compactRead ∨ Cont modulusRead readback compactRead)
                      (fun row : BHist =>
                        PkgSig bundle provenance pkg ∧ PkgSig bundle compactRead pkg ∧
                          hsame row compactRead)
                      hsame ∧
                    UnaryHistory publicRead ∧ UnaryHistory finiteCoverRead ∧
                      UnaryHistory locatedCoverRead ∧ UnaryHistory modulusRead ∧
                        UnaryHistory compactRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro packet publicRoute finiteRoute locatedRoute modulusRoute compactRoute compactPkg
  obtain ⟨_lowerUnary, _upperUnary, _orderUnary, _rationalUnary, dyadicUnary,
    streamUnary, readbackUnary, sealRowUnary, _transportUnary, _replayUnary,
    _provenanceUnary, localNameUnary, exportedUnary, _endpointRoute, _containmentRoute,
    _sealRoute, _transportRoute, _exportRoute, provenancePkg, _localNamePkg⟩ := packet
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed exportedUnary localNameUnary publicRoute
  have finiteUnary : UnaryHistory finiteCoverRead :=
    unary_cont_closed publicUnary dyadicUnary finiteRoute
  have locatedUnary : UnaryHistory locatedCoverRead :=
    unary_cont_closed finiteUnary streamUnary locatedRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed locatedUnary sealRowUnary modulusRoute
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed modulusUnary readbackUnary compactRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row compactRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row publicRead ∨ hsame row finiteCoverRead ∨
              hsame row locatedCoverRead ∨ hsame row modulusRead ∨
                hsame row compactRead ∨ Cont modulusRead readback compactRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle compactRead pkg ∧
              hsame row compactRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro compactRead ⟨hsame_refl compactRead, compactUnary⟩
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
                (Or.inl source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, compactPkg, source.left⟩
  }
  exact ⟨cert, publicUnary, finiteUnary, locatedUnary, modulusUnary, compactUnary⟩

end BEDC.Derived.ClosedboundedintervalUp
