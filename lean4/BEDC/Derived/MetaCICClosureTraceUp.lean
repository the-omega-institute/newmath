import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MetaCICClosureTraceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def MetaCICClosureTraceCarrier [AskSetup] [PackageSetup]
    (S U V B R G K H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory S ∧ UnaryHistory U ∧ UnaryHistory V ∧ UnaryHistory B ∧
    UnaryHistory R ∧ UnaryHistory G ∧ UnaryHistory K ∧ UnaryHistory H ∧
      UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧ Cont S U V ∧
        Cont V G K ∧ Cont B R C ∧ PkgSig bundle P pkg

theorem MetaCICClosureTraceCarrier_substitution_shift_generator_package
    [AskSetup] [PackageSetup] {S U V B R G K H C P N : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICClosureTraceCarrier S U V B R G K H C P N bundle pkg ->
      UnaryHistory S ∧ UnaryHistory U ∧ UnaryHistory V ∧ UnaryHistory G ∧
        Cont S U V ∧ Cont V G K ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier
  obtain ⟨SUnary, UUnary, VUnary, _BUnary, _RUnary, GUnary, _KUnary, _HUnary,
    _CUnary, _PUnary, _NUnary, shiftSubstitution, generatorPackage, _betaRoute,
    pkgSig⟩ := carrier
  exact ⟨SUnary, UUnary, VUnary, GUnary, shiftSubstitution, generatorPackage, pkgSig⟩

theorem MetaCICClosureTraceCarrier_beta_star_preservation_readback
    [AskSetup] [PackageSetup] {S U V B R G K H C P N betaRead routeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICClosureTraceCarrier S U V B R G K H C P N bundle pkg ->
      Cont B R betaRead ->
        Cont betaRead C routeRead ->
          hsame betaRead R ->
            UnaryHistory B ∧ UnaryHistory R ∧ UnaryHistory betaRead ∧
              UnaryHistory routeRead ∧ Cont B R betaRead ∧ Cont betaRead C routeRead ∧
                hsame betaRead R ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro carrier betaReadRoute routeReadRoute betaReadSame
  obtain ⟨_SUnary, _UUnary, _VUnary, BUnary, RUnary, _GUnary, _KUnary, _HUnary,
    CUnary, _PUnary, _NUnary, _shiftSubstitution, _generatorPackage, _betaRoute, pkgSig⟩ :=
    carrier
  have betaReadUnary : UnaryHistory betaRead :=
    unary_cont_closed BUnary RUnary betaReadRoute
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed betaReadUnary CUnary routeReadRoute
  exact
    ⟨BUnary, RUnary, betaReadUnary, routeReadUnary, betaReadRoute, routeReadRoute,
      betaReadSame, pkgSig⟩

theorem MetaCICClosureTraceCarrier_closed_substitution_route
    [AskSetup] [PackageSetup] {S U V B R G K H C P N closedSubst closedRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICClosureTraceCarrier S U V B R G K H C P N bundle pkg ->
      Cont S V closedSubst ->
        Cont closedSubst B closedRoute ->
          PkgSig bundle closedRoute pkg ->
            UnaryHistory S ∧ UnaryHistory V ∧ UnaryHistory B ∧
              UnaryHistory closedSubst ∧ UnaryHistory closedRoute ∧ Cont S U V ∧
                Cont S V closedSubst ∧ Cont closedSubst B closedRoute ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle closedRoute pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier closedSubstRoute closedRouteRoute closedRoutePkg
  obtain ⟨SUnary, _UUnary, VUnary, BUnary, _RUnary, _GUnary, _KUnary, _HUnary,
    _CUnary, _PUnary, _NUnary, shiftSubstitution, _generatorPackage, _betaRoute,
    pkgSig⟩ := carrier
  have closedSubstUnary : UnaryHistory closedSubst :=
    unary_cont_closed SUnary VUnary closedSubstRoute
  have closedRouteUnary : UnaryHistory closedRoute :=
    unary_cont_closed closedSubstUnary BUnary closedRouteRoute
  exact
    ⟨SUnary, VUnary, BUnary, closedSubstUnary, closedRouteUnary, shiftSubstitution,
      closedSubstRoute, closedRouteRoute, pkgSig, closedRoutePkg⟩

theorem MetaCICClosureTraceCarrier_namecert_obligations
    [AskSetup] [PackageSetup] {S U V B R G K H C P N : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICClosureTraceCarrier S U V B R G K H C P N bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          MetaCICClosureTraceCarrier S U V B R G K H C P N bundle pkg ∧ hsame row N)
        (fun row : BHist =>
          hsame row N ∧ Cont S U V ∧ Cont V G K ∧ Cont B R C)
        (fun row : BHist => hsame row N ∧ PkgSig bundle P pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert AskSetup PackageSetup PkgSig
  intro carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro N ⟨carrier, hsame_refl N⟩
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
        exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
    }
    pattern_sound := by
      intro _row source
      obtain
        ⟨_SUnary, _UUnary, _VUnary, _BUnary, _RUnary, _GUnary, _KUnary, _HUnary,
          _CUnary, _PUnary, _NUnary, shiftSubstitution, generatorPackage, betaRoute,
          _pkgSig⟩ := source.left
      exact ⟨source.right, shiftSubstitution, generatorPackage, betaRoute⟩
    ledger_sound := by
      intro _row source
      obtain
        ⟨_SUnary, _UUnary, _VUnary, _BUnary, _RUnary, _GUnary, _KUnary, _HUnary,
          _CUnary, _PUnary, _NUnary, _shiftSubstitution, _generatorPackage, _betaRoute,
          pkgSig⟩ := source.left
      exact ⟨source.right, pkgSig⟩
  }

theorem MetaCICClosureTraceCarrier_kernel_ledger_semantic_name_certificate
    [AskSetup] [PackageSetup] {S U V B R G K H C P N : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICClosureTraceCarrier S U V B R G K H C P N bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          MetaCICClosureTraceCarrier S U V B R G K H C P N bundle pkg ∧ hsame row K)
        (fun row : BHist => hsame row K ∧ Cont S U V ∧ Cont B R C)
        (fun row : BHist => hsame row K ∧ PkgSig bundle P pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert AskSetup PackageSetup PkgSig
  intro carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro K ⟨carrier, hsame_refl K⟩
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
        exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
    }
    pattern_sound := by
      intro _row source
      obtain
        ⟨_SUnary, _UUnary, _VUnary, _BUnary, _RUnary, _GUnary, _KUnary, _HUnary,
          _CUnary, _PUnary, _NUnary, shiftSubstitution, _generatorPackage, betaRoute,
          _pkgSig⟩ := source.left
      exact ⟨source.right, shiftSubstitution, betaRoute⟩
    ledger_sound := by
      intro _row source
      obtain
        ⟨_SUnary, _UUnary, _VUnary, _BUnary, _RUnary, _GUnary, _KUnary, _HUnary,
          _CUnary, _PUnary, _NUnary, _shiftSubstitution, _generatorPackage, _betaRoute,
          pkgSig⟩ := source.left
      exact ⟨source.right, pkgSig⟩
  }

theorem MetaCICClosureTraceCarrier_substitution_beta_chain_boundary
    [AskSetup] [PackageSetup] {S U V B R G K H C P N substRead betaRead combinedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICClosureTraceCarrier S U V B R G K H C P N bundle pkg ->
      Cont S V substRead ->
        Cont B R betaRead ->
          Cont substRead betaRead combinedRead ->
            UnaryHistory substRead ∧ UnaryHistory betaRead ∧
              UnaryHistory combinedRead ∧ Cont S U V ∧ Cont B R C ∧
                Cont substRead betaRead combinedRead ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier substRoute betaRoute combinedRoute
  obtain ⟨SUnary, _UUnary, VUnary, BUnary, RUnary, _GUnary, _KUnary, _HUnary,
    _CUnary, _PUnary, _NUnary, shiftSubstitution, _generatorPackage, betaCarrierRoute,
    pkgSig⟩ := carrier
  have substUnary : UnaryHistory substRead :=
    unary_cont_closed SUnary VUnary substRoute
  have betaUnary : UnaryHistory betaRead :=
    unary_cont_closed BUnary RUnary betaRoute
  have combinedUnary : UnaryHistory combinedRead :=
    unary_cont_closed substUnary betaUnary combinedRoute
  exact
    ⟨substUnary, betaUnary, combinedUnary, shiftSubstitution, betaCarrierRoute,
      combinedRoute, pkgSig⟩

theorem MetaCICClosureTraceCarrier_obligation_closure_package
    [AskSetup] [PackageSetup]
    {S U V B R G K H C P N betaRead routeRead closedSubst closedRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICClosureTraceCarrier S U V B R G K H C P N bundle pkg ->
      Cont B R betaRead ->
        Cont betaRead C routeRead ->
          Cont S V closedSubst ->
            Cont closedSubst B closedRoute ->
              PkgSig bundle routeRead pkg ->
                PkgSig bundle closedRoute pkg ->
                  UnaryHistory S ∧ UnaryHistory U ∧ UnaryHistory V ∧ UnaryHistory B ∧
                    UnaryHistory R ∧ UnaryHistory betaRead ∧ UnaryHistory routeRead ∧
                      UnaryHistory closedSubst ∧ UnaryHistory closedRoute ∧ Cont S U V ∧
                        Cont V G K ∧ Cont B R betaRead ∧ Cont betaRead C routeRead ∧
                          Cont S V closedSubst ∧ Cont closedSubst B closedRoute ∧
                            PkgSig bundle P pkg ∧ PkgSig bundle routeRead pkg ∧
                              PkgSig bundle closedRoute pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier betaReadRoute routeReadRoute closedSubstRoute closedRouteRoute routeReadPkg
    closedRoutePkg
  obtain ⟨SUnary, UUnary, VUnary, BUnary, RUnary, _GUnary, _KUnary, _HUnary,
    CUnary, _PUnary, _NUnary, shiftSubstitution, generatorPackage, _betaRoute, pkgSig⟩ :=
      carrier
  have betaReadUnary : UnaryHistory betaRead :=
    unary_cont_closed BUnary RUnary betaReadRoute
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed betaReadUnary CUnary routeReadRoute
  have closedSubstUnary : UnaryHistory closedSubst :=
    unary_cont_closed SUnary VUnary closedSubstRoute
  have closedRouteUnary : UnaryHistory closedRoute :=
    unary_cont_closed closedSubstUnary BUnary closedRouteRoute
  exact
    ⟨SUnary, UUnary, VUnary, BUnary, RUnary, betaReadUnary, routeReadUnary,
      closedSubstUnary, closedRouteUnary, shiftSubstitution, generatorPackage,
      betaReadRoute, routeReadRoute, closedSubstRoute, closedRouteRoute, pkgSig,
      routeReadPkg, closedRoutePkg⟩

theorem MetaCICClosureTraceCarrier_candidate_frontier
    [AskSetup] [PackageSetup] {S U V B R G K H C P N : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICClosureTraceCarrier S U V B R G K H C P N bundle pkg ->
      exists generatorRead : BHist, exists betaRead : BHist, exists frontierRead : BHist,
        UnaryHistory generatorRead ∧ UnaryHistory betaRead ∧ UnaryHistory frontierRead ∧
          hsame generatorRead (append (append S U) G) ∧
            hsame betaRead (append B R) ∧
              hsame frontierRead (append (append generatorRead betaRead) K) ∧
                Cont S U V ∧ Cont V G K ∧ Cont B R C ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle Pkg UnaryHistory
  intro carrier
  obtain ⟨SUnary, UUnary, _VUnary, BUnary, RUnary, GUnary, KUnary, _HUnary,
    _CUnary, _PUnary, _NUnary, shiftSubstitution, generatorPackage, betaRoute, pkgSig⟩ :=
      carrier
  let generatorRead := append (append S U) G
  let betaRead := append B R
  let frontierRead := append (append generatorRead betaRead) K
  have SUUnary : UnaryHistory (append S U) :=
    unary_append_closed SUnary UUnary
  have generatorUnary : UnaryHistory generatorRead :=
    unary_append_closed SUUnary GUnary
  have betaUnary : UnaryHistory betaRead :=
    unary_append_closed BUnary RUnary
  have generatorBetaUnary : UnaryHistory (append generatorRead betaRead) :=
    unary_append_closed generatorUnary betaUnary
  have frontierUnary : UnaryHistory frontierRead :=
    unary_append_closed generatorBetaUnary KUnary
  exact
    ⟨generatorRead, betaRead, frontierRead, generatorUnary, betaUnary, frontierUnary,
      hsame_refl generatorRead, hsame_refl betaRead, hsame_refl frontierRead,
      shiftSubstitution, generatorPackage, betaRoute, pkgSig⟩

end BEDC.Derived.MetaCICClosureTraceUp
