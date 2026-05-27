import BEDC.Derived.ClosedboundedintervalUp

namespace BEDC.Derived.ClosedboundedintervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedBoundedIntervalPacket_downstream_coverage_surface [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported netRead coverRead modulusRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback sealRow
        transport replay provenance localName exported bundle pkg ->
      UnaryHistory netRead ->
        Cont dyadic netRead coverRead ->
          Cont sealRow coverRead modulusRead ->
            PkgSig bundle modulusRead pkg ->
              UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory dyadic ∧
                UnaryHistory sealRow ∧ UnaryHistory coverRead ∧ UnaryHistory modulusRead ∧
                  Cont dyadic netRead coverRead ∧ Cont sealRow coverRead modulusRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle modulusRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet netReadUnary coverRoute modulusRoute modulusPkg
  obtain ⟨lowerUnary, upperUnary, _orderUnary, _rationalUnary, dyadicUnary,
    _streamUnary, _readbackUnary, sealRowUnary, _transportUnary, _replayUnary,
    _provenanceUnary, _localNameUnary, _exportedUnary, _endpointRoute,
    _containmentRoute, _sealRoute, _replayRoute, _nameRoute, provenancePkg,
    _localNamePkg⟩ := packet
  have coverReadUnary : UnaryHistory coverRead :=
    unary_cont_closed dyadicUnary netReadUnary coverRoute
  have modulusReadUnary : UnaryHistory modulusRead :=
    unary_cont_closed sealRowUnary coverReadUnary modulusRoute
  exact
    ⟨lowerUnary, upperUnary, dyadicUnary, sealRowUnary, coverReadUnary,
      modulusReadUnary, coverRoute, modulusRoute, provenancePkg, modulusPkg⟩

theorem ClosedBoundedIntervalPacket_dyadic_net_obligations [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported dyadicNetRead locatedRefinementRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback sealRow
        transport replay provenance localName exported bundle pkg ->
      Cont dyadic stream dyadicNetRead ->
        Cont dyadicNetRead sealRow locatedRefinementRead ->
          PkgSig bundle locatedRefinementRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row locatedRefinementRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row lower ∨ hsame row upper ∨ hsame row order ∨
                    hsame row rational ∨ hsame row dyadic ∨ hsame row stream ∨
                      hsame row readback ∨ hsame row sealRow ∨
                        Cont dyadicNetRead sealRow locatedRefinementRead)
                (fun row : BHist =>
                  PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg ∧
                    PkgSig bundle locatedRefinementRead pkg ∧ hsame row locatedRefinementRead)
                hsame ∧
              UnaryHistory dyadicNetRead ∧ UnaryHistory locatedRefinementRead ∧
                Cont dyadic stream dyadicNetRead ∧
                  Cont dyadicNetRead sealRow locatedRefinementRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet dyadicStreamNet netSealRefinement refinementPkg
  obtain ⟨_lowerUnary, _upperUnary, _orderUnary, _rationalUnary, dyadicUnary,
    streamUnary, _readbackUnary, sealRowUnary, _transportUnary, _replayUnary,
    _provenanceUnary, _localNameUnary, _exportedUnary, _endpointRoute,
    _containmentRoute, _sealRoute, _replayRoute, _nameRoute, provenancePkg,
    localNamePkg⟩ := packet
  have dyadicNetUnary : UnaryHistory dyadicNetRead :=
    unary_cont_closed dyadicUnary streamUnary dyadicStreamNet
  have locatedRefinementUnary : UnaryHistory locatedRefinementRead :=
    unary_cont_closed dyadicNetUnary sealRowUnary netSealRefinement
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row locatedRefinementRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row lower ∨ hsame row upper ∨ hsame row order ∨ hsame row rational ∨
              hsame row dyadic ∨ hsame row stream ∨ hsame row readback ∨
                hsame row sealRow ∨ Cont dyadicNetRead sealRow locatedRefinementRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg ∧
              PkgSig bundle locatedRefinementRead pkg ∧ hsame row locatedRefinementRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro locatedRefinementRead
        ⟨hsame_refl locatedRefinementRead, locatedRefinementUnary⟩
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
      intro _row _source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr netSealRefinement)))))))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, localNamePkg, refinementPkg, source.left⟩
  }
  exact ⟨cert, dyadicNetUnary, locatedRefinementUnary, dyadicStreamNet, netSealRefinement⟩

end BEDC.Derived.ClosedboundedintervalUp
