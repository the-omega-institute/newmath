import BEDC.Derived.MetacicDecidabilityWitnessUp.BridgeExport

namespace BEDC.Derived.MetacicDecidabilityWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetacicDecidabilityWitnessMatureNormalFormBoundary [AskSetup] [PackageSetup]
    {T S B F R H C P N checkerRead conversionRead publicRead bridgeRead exportRead
      matureRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicDecidabilityWitnessCarrier T S B F R H C P N bundle pkg →
      Cont T S checkerRead →
        Cont B F conversionRead →
          Cont checkerRead conversionRead publicRead →
            Cont publicRead N bridgeRead →
              Cont bridgeRead R exportRead →
                Cont exportRead F matureRead →
                  PkgSig bundle matureRead pkg →
                    SemanticNameCert
                        (fun row : BHist =>
                          hsame row matureRead ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
                        (fun row : BHist =>
                          hsame row T ∨ hsame row S ∨ hsame row B ∨ hsame row F ∨
                            hsame row R ∨ hsame row N ∨ hsame row matureRead)
                        (fun row : BHist =>
                          hsame row matureRead ∧ Cont T S checkerRead ∧
                            Cont B F conversionRead ∧
                              Cont checkerRead conversionRead publicRead ∧
                                Cont publicRead N bridgeRead ∧
                                  Cont bridgeRead R exportRead ∧
                                    Cont exportRead F matureRead ∧
                                      PkgSig bundle matureRead pkg)
                        hsame ∧
                      UnaryHistory exportRead ∧ UnaryHistory matureRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier checkerRoute conversionRoute publicRoute bridgeRoute exportRoute matureRoute
    maturePkg
  obtain ⟨tUnary, sUnary, bUnary, fUnary, rUnary, _hUnary, _cUnary, _pUnary,
    nUnary, _provenancePkg, _namePkg, _packetWitness⟩ := carrier
  have checkerUnary : UnaryHistory checkerRead :=
    unary_cont_closed tUnary sUnary checkerRoute
  have conversionUnary : UnaryHistory conversionRead :=
    unary_cont_closed bUnary fUnary conversionRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed checkerUnary conversionUnary publicRoute
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed publicUnary nUnary bridgeRoute
  have exportUnary : UnaryHistory exportRead :=
    unary_cont_closed bridgeUnary rUnary exportRoute
  have matureUnary : UnaryHistory matureRead :=
    unary_cont_closed exportUnary fUnary matureRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row matureRead ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
          (fun row : BHist =>
            hsame row T ∨ hsame row S ∨ hsame row B ∨ hsame row F ∨
              hsame row R ∨ hsame row N ∨ hsame row matureRead)
          (fun row : BHist =>
            hsame row matureRead ∧ Cont T S checkerRead ∧ Cont B F conversionRead ∧
              Cont checkerRead conversionRead publicRead ∧ Cont publicRead N bridgeRead ∧
                Cont bridgeRead R exportRead ∧ Cont exportRead F matureRead ∧
                  PkgSig bundle matureRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro matureRead ⟨hsame_refl matureRead, matureUnary, maturePkg⟩
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
        intro _row _other sameRows sourceRow
        cases sameRows
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.left, checkerRoute, conversionRoute, publicRoute, bridgeRoute,
          exportRoute, matureRoute, maturePkg⟩
  }
  exact ⟨cert, exportUnary, matureUnary⟩

end BEDC.Derived.MetacicDecidabilityWitnessUp
