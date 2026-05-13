import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FiniteTailDiagonalSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FiniteTailDiagonalSealCarrier [AskSetup] [PackageSetup]
    (precisionRow windowRow sourceRow witnessRow sealRow transportRow routeRow provenanceRow
      nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame
  UnaryHistory precisionRow ∧ UnaryHistory windowRow ∧ UnaryHistory sourceRow ∧
    UnaryHistory witnessRow ∧ UnaryHistory sealRow ∧ UnaryHistory transportRow ∧
      UnaryHistory routeRow ∧ UnaryHistory provenanceRow ∧ UnaryHistory nameRow ∧
        Cont precisionRow windowRow sourceRow ∧ Cont sourceRow witnessRow sealRow ∧
          Cont sealRow transportRow routeRow ∧ PkgSig bundle provenanceRow pkg ∧
            PkgSig bundle nameRow pkg

theorem FiniteTailDiagonalSealCarrier_window_lock [AskSetup] [PackageSetup]
    {precisionRow windowRow sourceRow witnessRow sealRow transportRow routeRow provenanceRow
      nameRow windowRow' sourceRow' sealRow' routeRow' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteTailDiagonalSealCarrier precisionRow windowRow sourceRow witnessRow sealRow
        transportRow routeRow provenanceRow nameRow bundle pkg ->
      hsame windowRow windowRow' ->
        Cont precisionRow windowRow' sourceRow' ->
          Cont sourceRow' witnessRow sealRow' ->
            Cont sealRow' transportRow routeRow' ->
              PkgSig bundle provenanceRow pkg ->
                FiniteTailDiagonalSealCarrier precisionRow windowRow' sourceRow'
                  witnessRow sealRow' transportRow routeRow' provenanceRow nameRow bundle pkg ∧
                hsame sourceRow sourceRow' ∧ hsame sealRow sealRow' ∧
                  hsame routeRow routeRow' := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame
  intro carrier sameWindow precisionWindowSource' sourceWitnessSeal' sealTransportRoute'
    provenancePkg
  obtain ⟨precisionUnary, windowUnary, sourceUnary, witnessUnary, sealUnary, transportUnary,
    routeUnary, provenanceUnary, nameUnary, precisionWindowSource, sourceWitnessSeal,
    sealTransportRoute, _oldProvenancePkg, namePkg⟩ := carrier
  have sameSource : hsame sourceRow sourceRow' :=
    cont_respects_hsame (hsame_refl precisionRow) sameWindow precisionWindowSource
      precisionWindowSource'
  have sameSeal : hsame sealRow sealRow' :=
    cont_respects_hsame sameSource (hsame_refl witnessRow) sourceWitnessSeal
      sourceWitnessSeal'
  have sameRoute : hsame routeRow routeRow' :=
    cont_respects_hsame sameSeal (hsame_refl transportRow) sealTransportRoute
      sealTransportRoute'
  have transported :
      FiniteTailDiagonalSealCarrier precisionRow windowRow' sourceRow' witnessRow sealRow'
        transportRow routeRow' provenanceRow nameRow bundle pkg := by
    exact
      ⟨precisionUnary, unary_transport windowUnary sameWindow,
        unary_transport sourceUnary sameSource, witnessUnary,
        unary_transport sealUnary sameSeal, transportUnary,
        unary_transport routeUnary sameRoute, provenanceUnary, nameUnary,
        precisionWindowSource', sourceWitnessSeal', sealTransportRoute', provenancePkg,
        namePkg⟩
  exact ⟨transported, sameSource, sameSeal, sameRoute⟩

theorem FiniteTailDiagonalSealCarrier_obligation_package [AskSetup] [PackageSetup]
    {precisionRow windowRow sourceRow witnessRow sealRow transportRow routeRow provenanceRow
      nameRow sealRead routeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteTailDiagonalSealCarrier precisionRow windowRow sourceRow witnessRow sealRow
        transportRow routeRow provenanceRow nameRow bundle pkg →
      Cont sourceRow witnessRow sealRead →
        Cont sealRead transportRow routeRead →
          PkgSig bundle routeRead pkg →
            UnaryHistory precisionRow ∧ UnaryHistory windowRow ∧ UnaryHistory sourceRow ∧
              UnaryHistory witnessRow ∧ UnaryHistory sealRow ∧ UnaryHistory sealRead ∧
                UnaryHistory routeRead ∧ Cont precisionRow windowRow sourceRow ∧
                  Cont sourceRow witnessRow sealRead ∧ Cont sealRead transportRow routeRead ∧
                    hsame sealRow sealRead ∧ hsame routeRow routeRead ∧
                      PkgSig bundle routeRead pkg ∧ PkgSig bundle nameRow pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier sourceWitnessSealRead sealReadTransportRouteRead routeReadPkg
  obtain ⟨precisionUnary, windowUnary, sourceUnary, witnessUnary, sealUnary, transportUnary,
    _routeUnary, _provenanceUnary, _nameUnary, precisionWindowSource, sourceWitnessSeal,
    sealTransportRoute, _provenancePkg, namePkg⟩ := carrier
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed sourceUnary witnessUnary sourceWitnessSealRead
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed sealReadUnary transportUnary sealReadTransportRouteRead
  have sameSeal : hsame sealRow sealRead :=
    cont_respects_hsame (hsame_refl sourceRow) (hsame_refl witnessRow) sourceWitnessSeal
      sourceWitnessSealRead
  have sameRoute : hsame routeRow routeRead :=
    cont_respects_hsame sameSeal (hsame_refl transportRow) sealTransportRoute
      sealReadTransportRouteRead
  exact
    ⟨precisionUnary, windowUnary, sourceUnary, witnessUnary, sealUnary, sealReadUnary,
      routeReadUnary, precisionWindowSource, sourceWitnessSealRead, sealReadTransportRouteRead,
      sameSeal, sameRoute, routeReadPkg, namePkg⟩

theorem FiniteTailDiagonalSealCarrier_selected_tail_exactness [AskSetup] [PackageSetup]
    {precisionRow windowRow sourceRow witnessRow sealRow transportRow routeRow provenanceRow
      nameRow witnessRow' sealRead routeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteTailDiagonalSealCarrier precisionRow windowRow sourceRow witnessRow sealRow
        transportRow routeRow provenanceRow nameRow bundle pkg ->
      hsame witnessRow witnessRow' ->
        Cont sourceRow witnessRow' sealRead ->
          Cont sealRead transportRow routeRead ->
            PkgSig bundle routeRead pkg ->
              hsame sealRow sealRead ∧ hsame routeRow routeRead ∧
                Cont sourceRow witnessRow' sealRead ∧ Cont sealRead transportRow routeRead ∧
                  PkgSig bundle nameRow pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier sameWitness sourceWitnessSealRead sealReadTransportRouteRead _routeReadPkg
  obtain ⟨_precisionUnary, _windowUnary, _sourceUnary, _witnessUnary, _sealUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _nameUnary, _precisionWindowSource,
    sourceWitnessSeal, sealTransportRoute, _provenancePkg, namePkg⟩ := carrier
  have sameSeal : hsame sealRow sealRead :=
    cont_respects_hsame (hsame_refl sourceRow) sameWitness sourceWitnessSeal
      sourceWitnessSealRead
  have sameRoute : hsame routeRow routeRead :=
    cont_respects_hsame sameSeal (hsame_refl transportRow) sealTransportRoute
      sealReadTransportRouteRead
  exact
    ⟨sameSeal, sameRoute, sourceWitnessSealRead, sealReadTransportRouteRead, namePkg⟩

theorem FiniteTailDiagonalSealCarrier_real_handoff [AskSetup] [PackageSetup]
    {precisionRow windowRow sourceRow witnessRow sealRow transportRow routeRow provenanceRow
      nameRow handoffRead routeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteTailDiagonalSealCarrier precisionRow windowRow sourceRow witnessRow sealRow
        transportRow routeRow provenanceRow nameRow bundle pkg ->
      Cont sourceRow witnessRow handoffRead ->
        Cont handoffRead transportRow routeRead ->
          PkgSig bundle handoffRead pkg ->
            PkgSig bundle routeRead pkg ->
              UnaryHistory precisionRow ∧ UnaryHistory windowRow ∧ UnaryHistory sourceRow ∧
                UnaryHistory witnessRow ∧ UnaryHistory handoffRead ∧ UnaryHistory routeRead ∧
                  Cont precisionRow windowRow sourceRow ∧ Cont sourceRow witnessRow handoffRead ∧
                    Cont handoffRead transportRow routeRead ∧ hsame sealRow handoffRead ∧
                      hsame routeRow routeRead ∧ PkgSig bundle handoffRead pkg ∧
                        PkgSig bundle routeRead pkg ∧ PkgSig bundle nameRow pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier sourceWitnessHandoff handoffTransportRoute handoffPkg routePkg
  obtain ⟨precisionUnary, windowUnary, sourceUnary, witnessUnary, _sealUnary, transportUnary,
    _routeUnary, _provenanceUnary, _nameUnary, precisionWindowSource, sourceWitnessSeal,
    sealTransportRoute, _provenancePkg, namePkg⟩ := carrier
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed sourceUnary witnessUnary sourceWitnessHandoff
  have routeUnary : UnaryHistory routeRead :=
    unary_cont_closed handoffUnary transportUnary handoffTransportRoute
  have sameSeal : hsame sealRow handoffRead :=
    cont_respects_hsame (hsame_refl sourceRow) (hsame_refl witnessRow) sourceWitnessSeal
      sourceWitnessHandoff
  have sameRoute : hsame routeRow routeRead :=
    cont_respects_hsame sameSeal (hsame_refl transportRow) sealTransportRoute
      handoffTransportRoute
  exact
    ⟨precisionUnary, windowUnary, sourceUnary, witnessUnary, handoffUnary, routeUnary,
      precisionWindowSource, sourceWitnessHandoff, handoffTransportRoute, sameSeal,
      sameRoute, handoffPkg, routePkg, namePkg⟩

end BEDC.Derived.FiniteTailDiagonalSealUp
