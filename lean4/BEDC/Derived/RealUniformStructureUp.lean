import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived

def RealUniformStructureUp : Type :=
  Unit

end BEDC.Derived

namespace BEDC.Derived.RealUniformStructureUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RealUniformStructureCarrier [AskSetup] [PackageSetup]
    (R M U F D S Q H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory R ∧
    UnaryHistory M ∧
      UnaryHistory U ∧
        UnaryHistory F ∧
          UnaryHistory D ∧
            UnaryHistory S ∧
              UnaryHistory Q ∧
                UnaryHistory H ∧
                  UnaryHistory C ∧
                    UnaryHistory P ∧
                      UnaryHistory N ∧ PkgSig bundle P pkg

theorem RealUniformStructureCarrier_metric_uniformity_handoff [AskSetup] [PackageSetup]
    {R M U F D S Q H C P N radiusRead entourageRead filterRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealUniformStructureCarrier R M U F D S Q H C P N bundle pkg →
      Cont R M radiusRead →
        Cont radiusRead D entourageRead →
          Cont entourageRead U filterRead →
            PkgSig bundle filterRead pkg →
              UnaryHistory R ∧ UnaryHistory M ∧ UnaryHistory radiusRead ∧
                UnaryHistory entourageRead ∧ UnaryHistory filterRead ∧
                  Cont R M radiusRead ∧ Cont radiusRead D entourageRead ∧
                    Cont entourageRead U filterRead ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle filterRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier radiusCont entourageCont filterCont filterPkg
  have rUnary : UnaryHistory R := carrier.left
  have mUnary : UnaryHistory M := carrier.right.left
  have uUnary : UnaryHistory U := carrier.right.right.left
  have dUnary : UnaryHistory D := carrier.right.right.right.right.left
  have pPkg : PkgSig bundle P pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.right
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed rUnary mUnary radiusCont
  have entourageUnary : UnaryHistory entourageRead :=
    unary_cont_closed radiusUnary dUnary entourageCont
  have filterUnary : UnaryHistory filterRead :=
    unary_cont_closed entourageUnary uUnary filterCont
  exact
    ⟨rUnary, mUnary, radiusUnary, entourageUnary, filterUnary, radiusCont,
      entourageCont, filterCont, pPkg, filterPkg⟩

theorem RealUniformStructureCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {R M U F D S Q H C P N routeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealUniformStructureCarrier R M U F D S Q H C P N bundle pkg ->
      Cont R M routeRead ->
        PkgSig bundle routeRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row R ∨ hsame row M ∨ hsame row U ∨ hsame row F ∨ hsame row D ∨
                  hsame row S ∨ hsame row Q ∨ hsame row routeRead)
              (fun row : BHist => hsame row routeRead ∧ PkgSig bundle routeRead pkg)
              hsame ∧
            UnaryHistory R ∧ UnaryHistory M ∧ UnaryHistory U ∧ UnaryHistory F ∧
              UnaryHistory D ∧ UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory routeRead ∧
                Cont R M routeRead ∧ PkgSig bundle routeRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier routeCont routePkg
  have rUnary : UnaryHistory R := carrier.left
  have mUnary : UnaryHistory M := carrier.right.left
  have uUnary : UnaryHistory U := carrier.right.right.left
  have fUnary : UnaryHistory F := carrier.right.right.right.left
  have dUnary : UnaryHistory D := carrier.right.right.right.right.left
  have sUnary : UnaryHistory S := carrier.right.right.right.right.right.left
  have qUnary : UnaryHistory Q := carrier.right.right.right.right.right.right.left
  have routeUnary : UnaryHistory routeRead :=
    unary_cont_closed rUnary mUnary routeCont
  have routeSource : hsame routeRead routeRead ∧ UnaryHistory routeRead :=
    ⟨hsame_refl routeRead, routeUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row R ∨ hsame row M ∨ hsame row U ∨ hsame row F ∨ hsame row D ∨
            hsame row S ∨ hsame row Q ∨ hsame row routeRead)
        (fun row : BHist => hsame row routeRead ∧ PkgSig bundle routeRead pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro routeRead routeSource
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
        intro _row _row' sameRows source
        exact ⟨hsame_trans (hsame_symm sameRows) source.left, unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, routePkg⟩
  }
  exact
    ⟨cert, rUnary, mUnary, uUnary, fUnary, dUnary, sUnary, qUnary, routeUnary, routeCont,
      routePkg⟩

end BEDC.Derived.RealUniformStructureUp
