import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealPowerSeriesUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RealPowerSeriesCarrier [AskSetup] [PackageSetup]
    (A Z X R W S M E H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory A ∧ UnaryHistory Z ∧ UnaryHistory X ∧ UnaryHistory R ∧
    UnaryHistory W ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory E ∧
      UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
        Cont A W S ∧ Cont R S M ∧ Cont M E C ∧ PkgSig bundle P pkg

theorem RealPowerSeriesCarrier_coefficient_window_obligation [AskSetup] [PackageSetup]
    {A Z X R W S M E H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealPowerSeriesCarrier A Z X R W S M E H C P N bundle pkg ->
      UnaryHistory A ∧ UnaryHistory W ∧ UnaryHistory S ∧ Cont A W S ∧
        PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier
  obtain ⟨AUnary, _ZUnary, _XUnary, _RUnary, WUnary, SUnary, _MUnary, _EUnary,
    _HUnary, _CUnary, _PUnary, _NUnary, coefficientWindow, _radiusMajorant,
    _majorantEndpoint, pkgSig⟩ := carrier
  exact ⟨AUnary, WUnary, SUnary, coefficientWindow, pkgSig⟩

theorem RealPowerSeriesCarrier_radius_window_handoff [AskSetup] [PackageSetup]
    {A Z X R W S M E H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealPowerSeriesCarrier A Z X R W S M E H C P N bundle pkg ->
      UnaryHistory A ∧ UnaryHistory W ∧ UnaryHistory S ∧ UnaryHistory R ∧
        UnaryHistory M ∧ UnaryHistory E ∧ UnaryHistory C ∧ Cont A W S ∧
          Cont R S M ∧ Cont M E C ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier
  obtain ⟨AUnary, _ZUnary, _XUnary, RUnary, WUnary, SUnary, MUnary, EUnary,
    _HUnary, CUnary, _PUnary, _NUnary, coefficientWindow, radiusMajorant,
    majorantEndpoint, pkgSig⟩ := carrier
  exact
    ⟨AUnary, WUnary, SUnary, RUnary, MUnary, EUnary, CUnary, coefficientWindow,
      radiusMajorant, majorantEndpoint, pkgSig⟩

theorem RealPowerSeriesCarrier_coefficient_window_transport [AskSetup] [PackageSetup]
    {A Z X R W S M E H C P N coeffRead partialRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealPowerSeriesCarrier A Z X R W S M E H C P N bundle pkg ->
      Cont A W coeffRead ->
        Cont coeffRead S partialRead ->
          hsame coeffRead W ->
            UnaryHistory A ∧ UnaryHistory W ∧ UnaryHistory S ∧
              UnaryHistory coeffRead ∧ UnaryHistory partialRead ∧
                Cont A W coeffRead ∧ Cont coeffRead S partialRead ∧
                  hsame coeffRead W ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro carrier coeffRoute partialRoute coeffSame
  obtain ⟨AUnary, _ZUnary, _XUnary, _RUnary, WUnary, SUnary, _MUnary, _EUnary,
    _HUnary, _CUnary, _PUnary, _NUnary, _coefficientWindow, _radiusMajorant,
    _majorantEndpoint, pkgSig⟩ := carrier
  have coeffReadUnary : UnaryHistory coeffRead :=
    unary_cont_closed AUnary WUnary coeffRoute
  have partialReadUnary : UnaryHistory partialRead :=
    unary_cont_closed coeffReadUnary SUnary partialRoute
  exact
    ⟨AUnary, WUnary, SUnary, coeffReadUnary, partialReadUnary, coeffRoute,
      partialRoute, coeffSame, pkgSig⟩

theorem RealPowerSeriesCarrier_majorant_regseqrat_budget [AskSetup] [PackageSetup]
    {A Z X R W S M E H C P N regBudget endpointRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealPowerSeriesCarrier A Z X R W S M E H C P N bundle pkg ->
      Cont S M regBudget ->
        Cont regBudget E endpointRead ->
          PkgSig bundle regBudget pkg ->
            PkgSig bundle endpointRead pkg ->
              UnaryHistory A ∧ UnaryHistory R ∧ UnaryHistory W ∧ UnaryHistory S ∧
                UnaryHistory M ∧ UnaryHistory E ∧ UnaryHistory regBudget ∧
                  UnaryHistory endpointRead ∧ Cont A W S ∧ Cont R S M ∧
                    Cont S M regBudget ∧ Cont regBudget E endpointRead ∧
                      PkgSig bundle P pkg ∧ PkgSig bundle regBudget pkg ∧
                        PkgSig bundle endpointRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier budgetRoute endpointRoute budgetPkg endpointPkg
  obtain ⟨AUnary, _ZUnary, _XUnary, RUnary, WUnary, SUnary, MUnary, EUnary,
    _HUnary, _CUnary, _PUnary, _NUnary, coefficientWindow, radiusMajorant,
    _majorantEndpoint, pkgSig⟩ := carrier
  have budgetUnary : UnaryHistory regBudget :=
    unary_cont_closed SUnary MUnary budgetRoute
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed budgetUnary EUnary endpointRoute
  exact
    ⟨AUnary, RUnary, WUnary, SUnary, MUnary, EUnary, budgetUnary, endpointUnary,
      coefficientWindow, radiusMajorant, budgetRoute, endpointRoute, pkgSig, budgetPkg,
      endpointPkg⟩

theorem RealPowerSeriesCarrier_regseqrat_endpoint_handoff [AskSetup] [PackageSetup]
    {A Z X R W S M E H C P N regBudget endpointRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealPowerSeriesCarrier A Z X R W S M E H C P N bundle pkg ->
      Cont S M regBudget ->
        Cont regBudget E endpointRead ->
          PkgSig bundle endpointRead pkg ->
            UnaryHistory A ∧ UnaryHistory R ∧ UnaryHistory W ∧ UnaryHistory S ∧
              UnaryHistory M ∧ UnaryHistory E ∧ UnaryHistory regBudget ∧
                UnaryHistory endpointRead ∧ Cont A W S ∧ Cont R S M ∧
                  Cont S M regBudget ∧ Cont regBudget E endpointRead ∧
                    PkgSig bundle P pkg ∧ PkgSig bundle endpointRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier budgetRoute endpointRoute endpointPkg
  obtain ⟨AUnary, _ZUnary, _XUnary, RUnary, WUnary, SUnary, MUnary, EUnary,
    _HUnary, _CUnary, _PUnary, _NUnary, coefficientWindow, radiusMajorant,
    _majorantEndpoint, pkgSig⟩ := carrier
  have budgetUnary : UnaryHistory regBudget :=
    unary_cont_closed SUnary MUnary budgetRoute
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed budgetUnary EUnary endpointRoute
  exact
    ⟨AUnary, RUnary, WUnary, SUnary, MUnary, EUnary, budgetUnary, endpointUnary,
      coefficientWindow, radiusMajorant, budgetRoute, endpointRoute, pkgSig, endpointPkg⟩

theorem RealPowerSeriesCarrier_endpoint_cauchy_budget [AskSetup] [PackageSetup]
    {A Z X R W S M E H C P N cauchyBudget endpointRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealPowerSeriesCarrier A Z X R W S M E H C P N bundle pkg ->
      Cont W S cauchyBudget ->
        Cont cauchyBudget E endpointRead ->
          PkgSig bundle cauchyBudget pkg ->
            PkgSig bundle endpointRead pkg ->
              UnaryHistory A ∧ UnaryHistory W ∧ UnaryHistory S ∧ UnaryHistory E ∧
                UnaryHistory cauchyBudget ∧ UnaryHistory endpointRead ∧ Cont A W S ∧
                  Cont W S cauchyBudget ∧ Cont cauchyBudget E endpointRead ∧
                    PkgSig bundle P pkg ∧ PkgSig bundle cauchyBudget pkg ∧
                      PkgSig bundle endpointRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier budgetRoute endpointRoute budgetPkg endpointPkg
  obtain ⟨AUnary, _ZUnary, _XUnary, _RUnary, WUnary, SUnary, _MUnary, EUnary,
    _HUnary, _CUnary, _PUnary, _NUnary, coefficientWindow, _radiusMajorant,
    _majorantEndpoint, pkgSig⟩ := carrier
  have budgetUnary : UnaryHistory cauchyBudget :=
    unary_cont_closed WUnary SUnary budgetRoute
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed budgetUnary EUnary endpointRoute
  exact
    ⟨AUnary, WUnary, SUnary, EUnary, budgetUnary, endpointUnary, coefficientWindow,
      budgetRoute, endpointRoute, pkgSig, budgetPkg, endpointPkg⟩

theorem RealPowerSeriesCarrier_partial_sum_majorant_readback [AskSetup] [PackageSetup]
    {A Z X R W S M E H C P N readback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealPowerSeriesCarrier A Z X R W S M E H C P N bundle pkg ->
      Cont S M readback ->
        UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory readback ∧ Cont S M readback ∧
          Cont R S M ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier readbackRoute
  obtain ⟨_AUnary, _ZUnary, _XUnary, _RUnary, _WUnary, SUnary, MUnary, _EUnary,
    _HUnary, _CUnary, _PUnary, _NUnary, _coefficientWindow, radiusMajorant,
    _majorantEndpoint, pkgSig⟩ := carrier
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed SUnary MUnary readbackRoute
  exact ⟨SUnary, MUnary, readbackUnary, readbackRoute, radiusMajorant, pkgSig⟩

theorem RealPowerSeriesCarrier_radius_source_compatibility [AskSetup] [PackageSetup]
    {A Z X R W S M E H C P N radiusRead sourceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealPowerSeriesCarrier A Z X R W S M E H C P N bundle pkg ->
      hsame radiusRead R ->
        hsame sourceRead A ->
          UnaryHistory radiusRead ∧ UnaryHistory sourceRead ∧ Cont A W S ∧
            Cont R S M ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle Pkg UnaryHistory
  intro carrier radiusSame sourceSame
  obtain ⟨AUnary, _ZUnary, _XUnary, RUnary, _WUnary, _SUnary, _MUnary, _EUnary,
    _HUnary, _CUnary, _PUnary, _NUnary, coefficientWindow, radiusMajorant,
    _majorantEndpoint, pkgSig⟩ := carrier
  have radiusReadUnary : UnaryHistory radiusRead :=
    unary_transport RUnary (hsame_symm radiusSame)
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_transport AUnary (hsame_symm sourceSame)
  exact ⟨radiusReadUnary, sourceReadUnary, coefficientWindow, radiusMajorant, pkgSig⟩

theorem RealPowerSeriesCarrier_terminal_real_seal_obligation [AskSetup] [PackageSetup]
    {A Z X R W S M E H C P N terminalSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealPowerSeriesCarrier A Z X R W S M E H C P N bundle pkg ->
      Cont E C terminalSeal ->
        PkgSig bundle terminalSeal pkg ->
          UnaryHistory A ∧ UnaryHistory Z ∧ UnaryHistory X ∧ UnaryHistory R ∧
            UnaryHistory W ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory E ∧
              UnaryHistory C ∧ UnaryHistory terminalSeal ∧ Cont A W S ∧
                Cont R S M ∧ Cont M E C ∧ Cont E C terminalSeal ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle terminalSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier terminalRoute terminalPkg
  obtain ⟨AUnary, ZUnary, XUnary, RUnary, WUnary, SUnary, MUnary, EUnary,
    _HUnary, CUnary, _PUnary, _NUnary, coefficientWindow, radiusMajorant,
    majorantEndpoint, pkgSig⟩ := carrier
  have terminalUnary : UnaryHistory terminalSeal :=
    unary_cont_closed EUnary CUnary terminalRoute
  exact
    ⟨AUnary, ZUnary, XUnary, RUnary, WUnary, SUnary, MUnary, EUnary, CUnary,
      terminalUnary, coefficientWindow, radiusMajorant, majorantEndpoint, terminalRoute,
      pkgSig, terminalPkg⟩

theorem RealPowerSeriesCarrier_nonescape [AskSetup] [PackageSetup]
    {A Z X R W S M E H C P N endpointRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealPowerSeriesCarrier A Z X R W S M E H C P N bundle pkg ->
      Cont S M endpointRead ->
        PkgSig bundle endpointRead pkg ->
          SemanticNameCert
              (fun row : BHist =>
                RealPowerSeriesCarrier A Z X R W S M E H C P N bundle pkg ∧
                  hsame row endpointRead)
              (fun row : BHist =>
                hsame row A ∨ hsame row W ∨ hsame row S ∨ hsame row M ∨
                  hsame row E ∨ hsame row endpointRead)
              (fun row : BHist => UnaryHistory row ∧ PkgSig bundle endpointRead pkg)
              hsame ∧
            UnaryHistory A ∧ UnaryHistory W ∧ UnaryHistory S ∧ UnaryHistory M ∧
              UnaryHistory E ∧ UnaryHistory endpointRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier endpointRoute endpointPkg
  have carrierPacket : RealPowerSeriesCarrier A Z X R W S M E H C P N bundle pkg :=
    carrier
  obtain ⟨AUnary, _ZUnary, _XUnary, _RUnary, WUnary, SUnary, MUnary, EUnary,
    _HUnary, _CUnary, _PUnary, _NUnary, _coefficientWindow, _radiusMajorant,
    _majorantEndpoint, _pkgSig⟩ := carrier
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed SUnary MUnary endpointRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            RealPowerSeriesCarrier A Z X R W S M E H C P N bundle pkg ∧
              hsame row endpointRead)
          (fun row : BHist =>
            hsame row A ∨ hsame row W ∨ hsame row S ∨ hsame row M ∨
              hsame row E ∨ hsame row endpointRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle endpointRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro endpointRead
          ⟨carrierPacket, hsame_refl endpointRead⟩
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
          exact ⟨sourceRow.left, hsame_trans (hsame_symm sameRows) sourceRow.right⟩
      }
      pattern_sound := by
        intro _row sourceRow
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.right))))
      ledger_sound := by
        intro row sourceRow
        exact ⟨unary_transport endpointUnary (hsame_symm sourceRow.right), endpointPkg⟩
    }
  exact ⟨cert, AUnary, WUnary, SUnary, MUnary, EUnary, endpointUnary⟩

theorem RealPowerSeriesCarrier_coefficient_shift_route [AskSetup] [PackageSetup]
    {A Z X R W S M E H C P N shiftedWindow shiftedPartial shiftedMajorant : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealPowerSeriesCarrier A Z X R W S M E H C P N bundle pkg ->
      Cont Z R shiftedWindow ->
        Cont shiftedWindow S shiftedPartial ->
          Cont shiftedPartial M shiftedMajorant ->
            UnaryHistory Z ∧ UnaryHistory R ∧ UnaryHistory shiftedWindow ∧
              UnaryHistory shiftedPartial ∧ UnaryHistory shiftedMajorant ∧
                Cont A W S ∧ Cont Z R shiftedWindow ∧
                  Cont shiftedWindow S shiftedPartial ∧
                    Cont shiftedPartial M shiftedMajorant ∧ Cont M E C ∧
                      PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier windowRoute partialRoute majorantRoute
  obtain ⟨_AUnary, ZUnary, _XUnary, RUnary, _WUnary, SUnary, MUnary, _EUnary,
    _HUnary, _CUnary, _PUnary, _NUnary, coefficientWindow, _radiusMajorant,
    majorantEndpoint, pkgSig⟩ := carrier
  have shiftedWindowUnary : UnaryHistory shiftedWindow :=
    unary_cont_closed ZUnary RUnary windowRoute
  have shiftedPartialUnary : UnaryHistory shiftedPartial :=
    unary_cont_closed shiftedWindowUnary SUnary partialRoute
  have shiftedMajorantUnary : UnaryHistory shiftedMajorant :=
    unary_cont_closed shiftedPartialUnary MUnary majorantRoute
  exact
    ⟨ZUnary, RUnary, shiftedWindowUnary, shiftedPartialUnary, shiftedMajorantUnary,
      coefficientWindow, windowRoute, partialRoute, majorantRoute, majorantEndpoint, pkgSig⟩

theorem RealPowerSeriesCarrier_cauchy_product_radius_budget [AskSetup] [PackageSetup]
    {A Z X R W S M E H C P N productWindow productMajorant productEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealPowerSeriesCarrier A Z X R W S M E H C P N bundle pkg ->
      Cont W S productWindow ->
        Cont productWindow M productMajorant ->
          Cont productMajorant E productEndpoint ->
            PkgSig bundle productEndpoint pkg ->
              UnaryHistory W ∧ UnaryHistory S ∧ UnaryHistory productWindow ∧
                UnaryHistory productMajorant ∧ UnaryHistory productEndpoint ∧
                  Cont A W S ∧ Cont W S productWindow ∧
                    Cont productWindow M productMajorant ∧
                      Cont productMajorant E productEndpoint ∧
                        PkgSig bundle P pkg ∧ PkgSig bundle productEndpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier productRoute majorantRoute endpointRoute endpointPkg
  obtain ⟨_AUnary, _ZUnary, _XUnary, _RUnary, WUnary, SUnary, MUnary, EUnary,
    _HUnary, _CUnary, _PUnary, _NUnary, coefficientWindow, _radiusMajorant,
    _majorantEndpoint, pkgSig⟩ := carrier
  have productWindowUnary : UnaryHistory productWindow :=
    unary_cont_closed WUnary SUnary productRoute
  have productMajorantUnary : UnaryHistory productMajorant :=
    unary_cont_closed productWindowUnary MUnary majorantRoute
  have productEndpointUnary : UnaryHistory productEndpoint :=
    unary_cont_closed productMajorantUnary EUnary endpointRoute
  exact
    ⟨WUnary, SUnary, productWindowUnary, productMajorantUnary, productEndpointUnary,
      coefficientWindow, productRoute, majorantRoute, endpointRoute, pkgSig, endpointPkg⟩

theorem RealPowerSeriesCarrier_stream_window_convergence_route [AskSetup] [PackageSetup]
    {A Z X R W S M E H C P N convergenceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealPowerSeriesCarrier A Z X R W S M E H C P N bundle pkg ->
      Cont W S convergenceRead ->
        PkgSig bundle convergenceRead pkg ->
          UnaryHistory W ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory E ∧
            UnaryHistory convergenceRead ∧ Cont A W S ∧ Cont W S convergenceRead ∧
              Cont R S M ∧ Cont M E C ∧ PkgSig bundle P pkg ∧
                PkgSig bundle convergenceRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier convergenceRoute convergencePkg
  obtain ⟨_AUnary, _ZUnary, _XUnary, _RUnary, WUnary, SUnary, MUnary, EUnary,
    _HUnary, _CUnary, _PUnary, _NUnary, coefficientWindow, radiusMajorant,
    majorantEndpoint, pkgSig⟩ := carrier
  have convergenceUnary : UnaryHistory convergenceRead :=
    unary_cont_closed WUnary SUnary convergenceRoute
  exact
    ⟨WUnary, SUnary, MUnary, EUnary, convergenceUnary, coefficientWindow,
      convergenceRoute, radiusMajorant, majorantEndpoint, pkgSig, convergencePkg⟩
theorem RealPowerSeriesCarrier_product_endpoint_nonescape [AskSetup] [PackageSetup]
    {A Z X R W S M E H C P N productRead endpointRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealPowerSeriesCarrier A Z X R W S M E H C P N bundle pkg ->
      Cont S M productRead ->
        Cont productRead E endpointRead ->
          PkgSig bundle endpointRead pkg ->
            SemanticNameCert
                (fun row : BHist =>
                  RealPowerSeriesCarrier A Z X R W S M E H C P N bundle pkg ∧
                    hsame row endpointRead)
                (fun row : BHist =>
                  hsame row A ∨ hsame row W ∨ hsame row S ∨ hsame row M ∨
                    hsame row E ∨ hsame row productRead ∨ hsame row endpointRead)
                (fun row : BHist => UnaryHistory row ∧ PkgSig bundle endpointRead pkg)
                hsame ∧
              UnaryHistory productRead ∧ UnaryHistory endpointRead ∧ Cont S M productRead ∧
                Cont productRead E endpointRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier productRoute endpointRoute endpointPkg
  have carrierPacket : RealPowerSeriesCarrier A Z X R W S M E H C P N bundle pkg :=
    carrier
  obtain ⟨AUnary, _ZUnary, _XUnary, _RUnary, WUnary, SUnary, MUnary, EUnary,
    _HUnary, _CUnary, _PUnary, _NUnary, _coefficientWindow, _radiusMajorant,
    _majorantEndpoint, _pkgSig⟩ := carrier
  have productUnary : UnaryHistory productRead :=
    unary_cont_closed SUnary MUnary productRoute
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed productUnary EUnary endpointRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            RealPowerSeriesCarrier A Z X R W S M E H C P N bundle pkg ∧
              hsame row endpointRead)
          (fun row : BHist =>
            hsame row A ∨ hsame row W ∨ hsame row S ∨ hsame row M ∨
              hsame row E ∨ hsame row productRead ∨ hsame row endpointRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle endpointRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro endpointRead
          ⟨carrierPacket, hsame_refl endpointRead⟩
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
          exact ⟨sourceRow.left, hsame_trans (hsame_symm sameRows) sourceRow.right⟩
      }
      pattern_sound := by
        intro _row sourceRow
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.right)))))
      ledger_sound := by
        intro row sourceRow
        exact ⟨unary_transport endpointUnary (hsame_symm sourceRow.right), endpointPkg⟩
    }
  exact ⟨cert, productUnary, endpointUnary, productRoute, endpointRoute⟩

theorem RealPowerSeriesObligationScope [AskSetup] [PackageSetup]
    {A Z X R W S M E H C P N radiusRead endpointRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealPowerSeriesCarrier A Z X R W S M E H C P N bundle pkg ->
      hsame radiusRead R ->
        Cont S M endpointRead ->
          PkgSig bundle endpointRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row endpointRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row A ∨ hsame row R ∨ hsame row W ∨ hsame row S ∨
                    hsame row M ∨ hsame row E ∨ hsame row endpointRead)
                (fun row : BHist => UnaryHistory row ∧ PkgSig bundle endpointRead pkg)
                hsame ∧
              UnaryHistory radiusRead ∧ UnaryHistory endpointRead ∧ Cont A W S ∧
                Cont R S M ∧ Cont S M endpointRead ∧ PkgSig bundle P pkg ∧
                  PkgSig bundle endpointRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont SemanticNameCert UnaryHistory
  intro carrier radiusSame endpointRoute endpointPkg
  obtain ⟨AUnary, _ZUnary, _XUnary, RUnary, WUnary, SUnary, MUnary, EUnary,
    _HUnary, _CUnary, _PUnary, _NUnary, coefficientWindow, radiusMajorant,
    _majorantEndpoint, pkgSig⟩ := carrier
  have radiusReadUnary : UnaryHistory radiusRead :=
    unary_transport RUnary (hsame_symm radiusSame)
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed SUnary MUnary endpointRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row endpointRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row A ∨ hsame row R ∨ hsame row W ∨ hsame row S ∨
              hsame row M ∨ hsame row E ∨ hsame row endpointRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle endpointRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro endpointRead ⟨hsame_refl endpointRead, endpointUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, endpointPkg⟩
  }
  exact
    ⟨cert, radiusReadUnary, endpointUnary, coefficientWindow, radiusMajorant,
      endpointRoute, pkgSig, endpointPkg⟩

theorem RealPowerSeriesCarrier_radius_subwindow_monotonicity [AskSetup] [PackageSetup]
    {A Z X R W S M E H C P N subwindow narrowedMajorant narrowedEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealPowerSeriesCarrier A Z X R W S M E H C P N bundle pkg ->
      hsame subwindow R ->
        Cont subwindow S narrowedMajorant ->
          Cont narrowedMajorant E narrowedEndpoint ->
            PkgSig bundle narrowedEndpoint pkg ->
              UnaryHistory subwindow ∧ UnaryHistory narrowedMajorant ∧
                UnaryHistory narrowedEndpoint ∧ Cont A W S ∧
                  Cont subwindow S narrowedMajorant ∧
                    Cont narrowedMajorant E narrowedEndpoint ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle narrowedEndpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro carrier subwindowSame majorantRoute endpointRoute endpointPkg
  obtain ⟨_AUnary, _ZUnary, _XUnary, RUnary, _WUnary, SUnary, _MUnary, EUnary,
    _HUnary, _CUnary, _PUnary, _NUnary, coefficientWindow, _radiusMajorant,
    _majorantEndpoint, pkgSig⟩ := carrier
  have subwindowUnary : UnaryHistory subwindow :=
    unary_transport RUnary (hsame_symm subwindowSame)
  have narrowedMajorantUnary : UnaryHistory narrowedMajorant :=
    unary_cont_closed subwindowUnary SUnary majorantRoute
  have narrowedEndpointUnary : UnaryHistory narrowedEndpoint :=
    unary_cont_closed narrowedMajorantUnary EUnary endpointRoute
  exact
    ⟨subwindowUnary, narrowedMajorantUnary, narrowedEndpointUnary, coefficientWindow,
      majorantRoute, endpointRoute, pkgSig, endpointPkg⟩

end BEDC.Derived.RealPowerSeriesUp
