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

theorem RealUniformStructureCarrier_l10_gate [AskSetup] [PackageSetup]
    {R M U F D S Q H C P N endpointRead radiusRead windowRead readbackRead filterRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealUniformStructureCarrier R M U F D S Q H C P N bundle pkg ->
      Cont R M endpointRead ->
        Cont endpointRead D radiusRead ->
          Cont radiusRead S windowRead ->
            Cont windowRead Q readbackRead ->
              Cont readbackRead U filterRead ->
                PkgSig bundle filterRead pkg ->
                  UnaryHistory endpointRead ∧ UnaryHistory radiusRead ∧
                    UnaryHistory windowRead ∧ UnaryHistory readbackRead ∧
                      UnaryHistory filterRead ∧ Cont R M endpointRead ∧
                        Cont endpointRead D radiusRead ∧ Cont radiusRead S windowRead ∧
                          Cont windowRead Q readbackRead ∧ Cont readbackRead U filterRead ∧
                            PkgSig bundle P pkg ∧ PkgSig bundle filterRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier endpointCont radiusCont windowCont readbackCont filterCont filterPkg
  have rUnary : UnaryHistory R := carrier.left
  have mUnary : UnaryHistory M := carrier.right.left
  have uUnary : UnaryHistory U := carrier.right.right.left
  have dUnary : UnaryHistory D := carrier.right.right.right.right.left
  have sUnary : UnaryHistory S := carrier.right.right.right.right.right.left
  have qUnary : UnaryHistory Q := carrier.right.right.right.right.right.right.left
  have pPkg : PkgSig bundle P pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.right
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed rUnary mUnary endpointCont
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed endpointUnary dUnary radiusCont
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed radiusUnary sUnary windowCont
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowUnary qUnary readbackCont
  have filterUnary : UnaryHistory filterRead :=
    unary_cont_closed readbackUnary uUnary filterCont
  exact
    ⟨endpointUnary, radiusUnary, windowUnary, readbackUnary, filterUnary, endpointCont,
      radiusCont, windowCont, readbackCont, filterCont, pPkg, filterPkg⟩

theorem RealUniformStructureCarrier_located_filter_compatibility [AskSetup] [PackageSetup]
    {R M U F D S Q H C P N locatedTail radiusRead windowRead readbackRead filterRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealUniformStructureCarrier R M U F D S Q H C P N bundle pkg ->
      Cont R D radiusRead ->
        Cont radiusRead U filterRead ->
          Cont filterRead S windowRead ->
            Cont windowRead Q readbackRead ->
              Cont readbackRead F locatedTail ->
                PkgSig bundle locatedTail pkg ->
                  UnaryHistory R ∧ UnaryHistory D ∧ UnaryHistory U ∧ UnaryHistory F ∧
                    UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory radiusRead ∧
                      UnaryHistory filterRead ∧ UnaryHistory windowRead ∧
                        UnaryHistory readbackRead ∧ UnaryHistory locatedTail ∧
                          Cont R D radiusRead ∧ Cont radiusRead U filterRead ∧
                            Cont filterRead S windowRead ∧ Cont windowRead Q readbackRead ∧
                              Cont readbackRead F locatedTail ∧ PkgSig bundle P pkg ∧
                                PkgSig bundle locatedTail pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier radiusCont filterCont windowCont readbackCont locatedCont locatedPkg
  have rUnary : UnaryHistory R := carrier.left
  have uUnary : UnaryHistory U := carrier.right.right.left
  have fUnary : UnaryHistory F := carrier.right.right.right.left
  have dUnary : UnaryHistory D := carrier.right.right.right.right.left
  have sUnary : UnaryHistory S := carrier.right.right.right.right.right.left
  have qUnary : UnaryHistory Q := carrier.right.right.right.right.right.right.left
  have pPkg : PkgSig bundle P pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.right
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed rUnary dUnary radiusCont
  have filterUnary : UnaryHistory filterRead :=
    unary_cont_closed radiusUnary uUnary filterCont
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed filterUnary sUnary windowCont
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowUnary qUnary readbackCont
  have locatedUnary : UnaryHistory locatedTail :=
    unary_cont_closed readbackUnary fUnary locatedCont
  exact
    ⟨rUnary, dUnary, uUnary, fUnary, sUnary, qUnary, radiusUnary, filterUnary,
      windowUnary, readbackUnary, locatedUnary, radiusCont, filterCont, windowCont,
      readbackCont, locatedCont, pPkg, locatedPkg⟩

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

theorem RealUniformStructureCarrier_filter_refinement_compatibility [AskSetup] [PackageSetup]
    {R M U F D S Q H C P N distanceRead radiusRead basisRead cauchyRead refinedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealUniformStructureCarrier R M U F D S Q H C P N bundle pkg ->
      Cont R M distanceRead -> Cont distanceRead D radiusRead -> Cont radiusRead U basisRead ->
        Cont basisRead F cauchyRead -> Cont cauchyRead H refinedRead ->
          PkgSig bundle refinedRead pkg ->
            UnaryHistory R ∧ UnaryHistory M ∧ UnaryHistory D ∧ UnaryHistory U ∧
              UnaryHistory F ∧ UnaryHistory H ∧ UnaryHistory distanceRead ∧
                UnaryHistory radiusRead ∧ UnaryHistory basisRead ∧ UnaryHistory cauchyRead ∧
                  UnaryHistory refinedRead ∧ Cont R M distanceRead ∧
                    Cont distanceRead D radiusRead ∧ Cont radiusRead U basisRead ∧
                      Cont basisRead F cauchyRead ∧ Cont cauchyRead H refinedRead ∧
                        PkgSig bundle P pkg ∧ PkgSig bundle refinedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier distanceCont radiusCont basisCont cauchyCont refinedCont refinedPkg
  have rUnary : UnaryHistory R := carrier.left
  have mUnary : UnaryHistory M := carrier.right.left
  have uUnary : UnaryHistory U := carrier.right.right.left
  have fUnary : UnaryHistory F := carrier.right.right.right.left
  have dUnary : UnaryHistory D := carrier.right.right.right.right.left
  have hUnary : UnaryHistory H := carrier.right.right.right.right.right.right.right.left
  have pPkg : PkgSig bundle P pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.right
  have distanceUnary : UnaryHistory distanceRead :=
    unary_cont_closed rUnary mUnary distanceCont
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed distanceUnary dUnary radiusCont
  have basisUnary : UnaryHistory basisRead :=
    unary_cont_closed radiusUnary uUnary basisCont
  have cauchyUnary : UnaryHistory cauchyRead :=
    unary_cont_closed basisUnary fUnary cauchyCont
  have refinedUnary : UnaryHistory refinedRead :=
    unary_cont_closed cauchyUnary hUnary refinedCont
  exact
    ⟨rUnary, mUnary, dUnary, uUnary, fUnary, hUnary, distanceUnary, radiusUnary,
      basisUnary, cauchyUnary, refinedUnary, distanceCont, radiusCont, basisCont,
      cauchyCont, refinedCont, pPkg, refinedPkg⟩

end BEDC.Derived.RealUniformStructureUp
