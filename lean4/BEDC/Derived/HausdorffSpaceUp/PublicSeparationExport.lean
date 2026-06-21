import BEDC.Derived.HausdorffSpaceUp.TasteGate

namespace BEDC.Derived.HausdorffSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HausdorffSpaceCarrier_public_separation_export [AskSetup] [PackageSetup]
    {T x y U V D M E H C P N metricRead classifierRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HausdorffSpaceCarrier T x y U V D M E H C P N bundle pkg ->
      Cont M E metricRead ->
        Cont metricRead H classifierRead ->
          Cont classifierRead N publicRead ->
            PkgSig bundle publicRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row T ∨ hsame row x ∨ hsame row y ∨ hsame row U ∨
                      hsame row V ∨ hsame row D ∨ hsame row M ∨ hsame row E ∨
                        hsame row metricRead ∨ hsame row classifierRead ∨
                          hsame row publicRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont M E metricRead ∧
                      Cont metricRead H classifierRead ∧
                        Cont classifierRead N publicRead ∧ PkgSig bundle publicRead pkg)
                  hsame ∧
                UnaryHistory metricRead ∧ UnaryHistory classifierRead ∧
                  UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig Cont SemanticNameCert hsame UnaryHistory
  intro carrier metricRoute classifierRoute publicRoute packageRead
  obtain ⟨_tUnary, _xUnary, _yUnary, _uUnary, _vUnary, _dUnary, mUnary, eUnary,
    hUnary, _cUnary, _pUnary, nUnary, _pointRoute, _classifierRoute,
    _separationRoute, _metricCarrierRoute, _pkgRow⟩ := carrier
  have metricUnary : UnaryHistory metricRead :=
    unary_cont_closed mUnary eUnary metricRoute
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed metricUnary hUnary classifierRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed classifierUnary nUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row x ∨ hsame row y ∨ hsame row U ∨ hsame row V ∨
              hsame row D ∨ hsame row M ∨ hsame row E ∨ hsame row metricRead ∨
                hsame row classifierRead ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M E metricRead ∧ Cont metricRead H classifierRead ∧
              Cont classifierRead N publicRead ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inr <| Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, metricRoute, classifierRoute, publicRoute, packageRead⟩
  }
  exact ⟨cert, metricUnary, classifierUnary, publicUnary⟩

theorem HausdorffSpacePublicSeparationExport [AskSetup] [PackageSetup]
    {T x y U V D M E H C P N metricReplay classifierReplay pointReplay realReplay
      publicReplay : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory T ->
      UnaryHistory x ->
        UnaryHistory y ->
          UnaryHistory U ->
            UnaryHistory V ->
              UnaryHistory D ->
                UnaryHistory M ->
                  UnaryHistory E ->
                    UnaryHistory H ->
                      UnaryHistory C ->
                        UnaryHistory P ->
                          UnaryHistory N ->
                            Cont M E metricReplay ->
                              Cont U V classifierReplay ->
                                Cont classifierReplay D pointReplay ->
                                  Cont pointReplay E realReplay ->
                                    Cont realReplay N publicReplay ->
                                      PkgSig bundle P pkg ->
                                        SemanticNameCert
                                            (fun row : BHist =>
                                              hsame row publicReplay ∧ UnaryHistory row)
                                            (fun row : BHist =>
                                              hsame row T ∨ hsame row x ∨
                                                hsame row y ∨ hsame row U ∨
                                                  hsame row V ∨ hsame row D ∨
                                                    hsame row M ∨ hsame row E ∨
                                                      hsame row H ∨ hsame row C ∨
                                                        hsame row P ∨ hsame row N ∨
                                                          hsame row metricReplay ∨
                                                            hsame row classifierReplay ∨
                                                              hsame row pointReplay ∨
                                                                hsame row realReplay ∨
                                                                  hsame row publicReplay)
                                            (fun row : BHist =>
                                              UnaryHistory row ∧
                                                Cont M E metricReplay ∧
                                                  Cont U V classifierReplay ∧
                                                    Cont classifierReplay D pointReplay ∧
                                                      Cont pointReplay E realReplay ∧
                                                        Cont realReplay N publicReplay ∧
                                                          PkgSig bundle P pkg)
                                            hsame ∧
                                          UnaryHistory metricReplay ∧
                                            UnaryHistory classifierReplay ∧
                                              UnaryHistory pointReplay ∧
                                                UnaryHistory realReplay ∧
                                                  UnaryHistory publicReplay := by
  -- BEDC touchpoint anchor: HausdorffSpaceUp BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro rowsT rowsX rowsY rowsU rowsV rowsD rowsM rowsE rowsH rowsC rowsP rowsN
    metricRoute classifierRoute pointRoute realRoute publicRoute packageRead
  have metricUnary : UnaryHistory metricReplay :=
    unary_cont_closed rowsM rowsE metricRoute
  have classifierUnary : UnaryHistory classifierReplay :=
    unary_cont_closed rowsU rowsV classifierRoute
  have pointUnary : UnaryHistory pointReplay :=
    unary_cont_closed classifierUnary rowsD pointRoute
  have realUnary : UnaryHistory realReplay :=
    unary_cont_closed pointUnary rowsE realRoute
  have publicUnary : UnaryHistory publicReplay :=
    unary_cont_closed realUnary rowsN publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicReplay ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row x ∨ hsame row y ∨ hsame row U ∨ hsame row V ∨
              hsame row D ∨ hsame row M ∨ hsame row E ∨ hsame row H ∨ hsame row C ∨
                hsame row P ∨ hsame row N ∨ hsame row metricReplay ∨
                  hsame row classifierReplay ∨ hsame row pointReplay ∨
                    hsame row realReplay ∨ hsame row publicReplay)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M E metricReplay ∧ Cont U V classifierReplay ∧
              Cont classifierReplay D pointReplay ∧ Cont pointReplay E realReplay ∧
                Cont realReplay N publicReplay ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro publicReplay ⟨hsame_refl publicReplay, publicUnary⟩
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
          Or.inr <| Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, metricRoute, classifierRoute, pointRoute, realRoute,
          publicRoute, packageRead⟩
  }
  exact
    ⟨cert, metricUnary, classifierUnary, pointUnary, realUnary, publicUnary⟩

end BEDC.Derived.HausdorffSpaceUp
