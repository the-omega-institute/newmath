import BEDC.Derived.CauchyProductUp
import BEDC.Derived.RealseriesUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CauchyProductUp

open BEDC.Derived.RealseriesUp
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_mature_public_factorization [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name seriesTerm seriesPartial seriesWindow
      seriesReadback seriesDyadic seriesThreshold seriesTransport seriesReplay seriesProvenance
      seriesCert seriesTail seriesSeal publicSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      RealSeriesRootCauchyProductSurface seriesTerm seriesPartial seriesWindow seriesReadback
        seriesDyadic seriesThreshold seriesTransport seriesReplay seriesProvenance seriesCert
        bundle pkg ->
        Cont classifier routes seriesTail ->
          Cont seriesTail ledger seriesSeal ->
            Cont seriesSeal routes publicSeal ->
              PkgSig bundle publicSeal pkg ->
                SemanticNameCert
                    (fun row : BHist =>
                      hsame row product ∨ hsame row classifier ∨ hsame row seriesTail ∨
                        hsame row seriesSeal ∨ hsame row publicSeal ∨
                          hsame row seriesReadback)
                    (fun row : BHist =>
                      hsame row product ∨ hsame row classifier ∨ hsame row seriesTail ∨
                        hsame row seriesSeal ∨ hsame row publicSeal ∨
                          hsame row seriesReadback)
                    (fun row : BHist =>
                      PkgSig bundle publicSeal pkg ∧
                        (hsame row product ∨ hsame row classifier ∨ hsame row seriesTail ∨
                          hsame row seriesSeal ∨ hsame row publicSeal ∨
                            hsame row seriesReadback))
                    hsame ∧
                  UnaryHistory product ∧ UnaryHistory classifier ∧ UnaryHistory seriesTail ∧
                    UnaryHistory seriesSeal ∧ UnaryHistory publicSeal ∧
                      UnaryHistory seriesReadback ∧ Cont observationA observationB product ∧
                        Cont product ledger classifier ∧ Cont classifier routes seriesTail ∧
                          Cont seriesTail ledger seriesSeal ∧
                            Cont seriesSeal routes publicSeal ∧ PkgSig bundle name pkg ∧
                              PkgSig bundle publicSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame UnaryHistory
  intro packet seriesSurface classifierTail tailSeal sealPublic publicSealPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, _windowAUnary, _windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    _windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  obtain ⟨_termUnary, _partialUnary, _windowUnary, seriesReadbackUnary, _dyadicUnary,
    _thresholdUnary, _transportUnary, _replayUnary, _provenanceUnary, _certUnary,
    _readbackDyadicThreshold, _provenancePkg⟩ := seriesSurface
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have seriesTailUnary : UnaryHistory seriesTail :=
    unary_cont_closed classifierUnary routesUnary classifierTail
  have seriesSealUnary : UnaryHistory seriesSeal :=
    unary_cont_closed seriesTailUnary ledgerUnary tailSeal
  have publicSealUnary : UnaryHistory publicSeal :=
    unary_cont_closed seriesSealUnary routesUnary sealPublic
  have sourceAtProduct :
      hsame product product ∨ hsame product classifier ∨ hsame product seriesTail ∨
        hsame product seriesSeal ∨ hsame product publicSeal ∨ hsame product seriesReadback :=
    Or.inl (hsame_refl product)
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row product ∨ hsame row classifier ∨ hsame row seriesTail ∨
              hsame row seriesSeal ∨ hsame row publicSeal ∨ hsame row seriesReadback)
          (fun row : BHist =>
            hsame row product ∨ hsame row classifier ∨ hsame row seriesTail ∨
              hsame row seriesSeal ∨ hsame row publicSeal ∨ hsame row seriesReadback)
          (fun row : BHist =>
            PkgSig bundle publicSeal pkg ∧
              (hsame row product ∨ hsame row classifier ∨ hsame row seriesTail ∨
                hsame row seriesSeal ∨ hsame row publicSeal ∨ hsame row seriesReadback))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro product sourceAtProduct
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
        cases sameRows
        exact source
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact ⟨publicSealPkg, source⟩
  }
  exact
    ⟨cert, productUnary, classifierUnary, seriesTailUnary, seriesSealUnary,
      publicSealUnary, seriesReadbackUnary, productRoute, classifierRoute, classifierTail,
      tailSeal, sealPublic, namePkg, publicSealPkg⟩

end BEDC.Derived.CauchyProductUp
