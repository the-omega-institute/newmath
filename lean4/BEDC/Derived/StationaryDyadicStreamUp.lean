import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

inductive StationaryDyadicStreamUp : Type where
  | packet : StationaryDyadicStreamUp

namespace StationaryDyadicStreamUp

def StationaryDyadicStreamCarrier [AskSetup] [PackageSetup]
    (D W R E H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  UnaryHistory D ∧ UnaryHistory W ∧ UnaryHistory R ∧ UnaryHistory E ∧
    UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
      Cont D W R ∧ Cont W R E ∧ Cont R E C ∧ Cont C P N ∧
        PkgSig bundle N pkg

theorem StationaryDyadicStreamCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {D W R E H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StationaryDyadicStreamCarrier D W R E H C P N bundle pkg ->
      SemanticNameCert
        (fun row : BHist => hsame row N ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
        (fun row : BHist => Cont C P row ∧ Cont D W R ∧ Cont W R E)
        (fun row : BHist => PkgSig bundle row pkg ∧ Cont R E C ∧ Cont C P N)
        (fun row row' : BHist => hsame row row') := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier
  obtain ⟨_unaryD, _unaryW, _unaryR, _unaryE, _unaryH, _unaryC, _unaryP, unaryN,
    routeDWR, routeWRE, routeREC, routeCPN, pkgN⟩ := carrier
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro N ⟨hsame_refl N, unaryN, pkgN⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _row' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        cases sameRows
        exact source
    }
    pattern_sound := by
      intro row source
      cases source.left
      exact ⟨routeCPN, routeDWR, routeWRE⟩
    ledger_sound := by
      intro row source
      exact ⟨source.right.right, routeREC, routeCPN⟩
  }

theorem StationaryDyadicStreamCarrier_constant_embedding [AskSetup] [PackageSetup]
    {D W R E H C P N sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StationaryDyadicStreamCarrier D W R E H C P N bundle pkg ->
      Cont E H sealRead ->
        PkgSig bundle sealRead pkg ->
          UnaryHistory D ∧ UnaryHistory W ∧ UnaryHistory R ∧ UnaryHistory E ∧
            UnaryHistory sealRead ∧ Cont D W R ∧ Cont W R E ∧ Cont E H sealRead ∧
              PkgSig bundle N pkg ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory ProbeBundle PkgSig
  intro carrier routeSeal pkgSeal
  obtain ⟨unaryD, unaryW, unaryR, unaryE, unaryH, _unaryC, _unaryP, _unaryN,
    routeDWR, routeWRE, _routeREC, _routeCPN, pkgN⟩ := carrier
  have unarySeal : UnaryHistory sealRead :=
    unary_cont_closed unaryE unaryH routeSeal
  exact
    ⟨unaryD, unaryW, unaryR, unaryE, unarySeal, routeDWR, routeWRE, routeSeal,
      pkgN, pkgSeal⟩

theorem StationaryDyadicStreamCarrier_real_seal_boundary [AskSetup] [PackageSetup]
    {D W R E H C P N sealRead terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StationaryDyadicStreamCarrier D W R E H C P N bundle pkg →
      Cont E H sealRead →
        Cont sealRead P terminal →
          PkgSig bundle terminal pkg →
            UnaryHistory D ∧ UnaryHistory W ∧ UnaryHistory R ∧ UnaryHistory E ∧
              UnaryHistory sealRead ∧ UnaryHistory terminal ∧ Cont D W R ∧
                Cont W R E ∧ Cont E H sealRead ∧ Cont sealRead P terminal ∧
                  PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory ProbeBundle PkgSig
  intro carrier sealRoute terminalRoute terminalPkg
  obtain ⟨unaryD, unaryW, unaryR, unaryE, unaryH, _unaryC, unaryP, _unaryN,
    routeDWR, routeWRE, _routeREC, _routeCPN, _pkgN⟩ := carrier
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed unaryE unaryH sealRoute
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed sealUnary unaryP terminalRoute
  exact
    ⟨unaryD, unaryW, unaryR, unaryE, sealUnary, terminalUnary, routeDWR, routeWRE,
      sealRoute, terminalRoute, terminalPkg⟩

end StationaryDyadicStreamUp

end BEDC.Derived
