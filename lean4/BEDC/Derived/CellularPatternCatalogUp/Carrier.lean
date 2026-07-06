import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CellularPatternCatalogUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CellularPatternCatalogCarrier [AskSetup] [PackageSetup]
    (R W T G H C P N ruleWindowRead catalogRead tagRead : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory R ∧ UnaryHistory W ∧ UnaryHistory G ∧ UnaryHistory T ∧
    Cont R W ruleWindowRead ∧ Cont ruleWindowRead G catalogRead ∧
      Cont catalogRead T tagRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem CellularPatternCatalogCarrier_route_closure [AskSetup] [PackageSetup]
    {R W T G H C P N ruleWindowRead catalogRead tagRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CellularPatternCatalogCarrier R W T G H C P N ruleWindowRead catalogRead tagRead
        bundle pkg →
      UnaryHistory ruleWindowRead ∧ UnaryHistory catalogRead ∧ UnaryHistory tagRead ∧
        PkgSig bundle P pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier
  obtain ⟨unaryR, unaryW, unaryG, unaryT, ruleWindowRoute, catalogRoute, tagRoute,
    pkgP, pkgN⟩ := carrier
  have ruleWindowUnary : UnaryHistory ruleWindowRead :=
    unary_cont_closed unaryR unaryW ruleWindowRoute
  have catalogUnary : UnaryHistory catalogRead :=
    unary_cont_closed ruleWindowUnary unaryG catalogRoute
  have tagUnary : UnaryHistory tagRead :=
    unary_cont_closed catalogUnary unaryT tagRoute
  exact ⟨ruleWindowUnary, catalogUnary, tagUnary, pkgP, pkgN⟩

theorem CellularPatternCatalog_public_lookup_surface [AskSetup] [PackageSetup]
    {R W T G H C P N ruleWindowRead catalogRead tagRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CellularPatternCatalogCarrier R W T G H C P N ruleWindowRead catalogRead tagRead
        bundle pkg →
      UnaryHistory N →
        Cont tagRead N publicRead →
          PkgSig bundle N pkg →
            SemanticNameCert
                (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row R ∨ hsame row W ∨ hsame row G ∨ hsame row T ∨
                    hsame row ruleWindowRead ∨ hsame row catalogRead ∨
                      hsame row tagRead ∨ hsame row publicRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont R W ruleWindowRead ∧
                    Cont ruleWindowRead G catalogRead ∧ Cont catalogRead T tagRead ∧
                      Cont tagRead N publicRead ∧ PkgSig bundle N pkg)
                hsame ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier nameUnary publicRoute pkgN
  obtain ⟨unaryR, unaryW, unaryG, unaryT, ruleWindowRoute, catalogRoute, tagRoute,
    _pkgP, _carrierPkgN⟩ := carrier
  have ruleWindowUnary : UnaryHistory ruleWindowRead :=
    unary_cont_closed unaryR unaryW ruleWindowRoute
  have catalogUnary : UnaryHistory catalogRead :=
    unary_cont_closed ruleWindowUnary unaryG catalogRoute
  have tagUnary : UnaryHistory tagRead :=
    unary_cont_closed catalogUnary unaryT tagRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed tagUnary nameUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row R ∨ hsame row W ∨ hsame row G ∨ hsame row T ∨
              hsame row ruleWindowRead ∨ hsame row catalogRead ∨
                hsame row tagRead ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont R W ruleWindowRead ∧
              Cont ruleWindowRead G catalogRead ∧ Cont catalogRead T tagRead ∧
                Cont tagRead N publicRead ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead
        ⟨hsame_refl publicRead, publicUnary⟩
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
        intro _row _other sameRows sourceData
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceData.left,
            unary_transport sourceData.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceData
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr sourceData.left))))))
    ledger_sound := by
      intro _row sourceData
      exact
        ⟨sourceData.right, ruleWindowRoute, catalogRoute, tagRoute, publicRoute, pkgN⟩
  }
  exact ⟨cert, publicUnary⟩

theorem CellularPatternCatalog_mature_boundary [AskSetup] [PackageSetup]
    {R W T G H C P N ruleWindowRead catalogRead tagRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CellularPatternCatalogCarrier R W T G H C P N ruleWindowRead catalogRead tagRead
        bundle pkg →
      UnaryHistory N →
        Cont tagRead N publicRead →
          PkgSig bundle N pkg →
            SemanticNameCert
                  (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row R ∨ hsame row W ∨ hsame row G ∨ hsame row T ∨
                      hsame row ruleWindowRead ∨ hsame row catalogRead ∨
                        hsame row tagRead ∨ hsame row publicRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont R W ruleWindowRead ∧
                      Cont ruleWindowRead G catalogRead ∧ Cont catalogRead T tagRead ∧
                        Cont tagRead N publicRead ∧ PkgSig bundle N pkg)
                  hsame ∧
              UnaryHistory ruleWindowRead ∧ UnaryHistory catalogRead ∧
                UnaryHistory tagRead ∧ UnaryHistory publicRead ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier nameUnary publicRoute pkgN
  have routeClosure :=
    CellularPatternCatalogCarrier_route_closure (R := R) (W := W) (T := T) (G := G)
      (H := H) (C := C) (P := P) (N := N) (ruleWindowRead := ruleWindowRead)
      (catalogRead := catalogRead) (tagRead := tagRead) (bundle := bundle) (pkg := pkg)
      carrier
  have publicSurface :=
    CellularPatternCatalog_public_lookup_surface (R := R) (W := W) (T := T) (G := G)
      (H := H) (C := C) (P := P) (N := N) (ruleWindowRead := ruleWindowRead)
      (catalogRead := catalogRead) (tagRead := tagRead) (publicRead := publicRead)
      (bundle := bundle) (pkg := pkg) carrier nameUnary publicRoute pkgN
  rcases routeClosure with ⟨ruleWindowUnary, catalogUnary, tagUnary, pkgP, _pkgN⟩
  rcases publicSurface with ⟨publicCert, publicUnary⟩
  exact ⟨publicCert, ruleWindowUnary, catalogUnary, tagUnary, publicUnary, pkgP, pkgN⟩

end BEDC.Derived.CellularPatternCatalogUp
