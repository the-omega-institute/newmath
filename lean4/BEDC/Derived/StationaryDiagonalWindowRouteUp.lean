import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.StationaryDiagonalWindowRouteUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def StationaryDiagonalWindowRoutePacket [AskSetup] [PackageSetup]
    (ratSeed streamWindow sealRow dyadicLedger realWindow transports routes provenance name :
      BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory ratSeed ∧ UnaryHistory streamWindow ∧ UnaryHistory sealRow ∧
    UnaryHistory dyadicLedger ∧ UnaryHistory realWindow ∧ UnaryHistory transports ∧
      UnaryHistory routes ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
        Cont ratSeed streamWindow sealRow ∧ Cont streamWindow dyadicLedger realWindow ∧
          Cont realWindow transports routes ∧ Cont routes provenance name ∧
            PkgSig bundle name pkg

theorem StationaryDiagonalWindowRoutePacket_namecert_obligations
    [AskSetup] [PackageSetup]
    {ratSeed streamWindow sealRow dyadicLedger realWindow transports routes provenance name :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StationaryDiagonalWindowRoutePacket ratSeed streamWindow sealRow dyadicLedger realWindow
        transports routes provenance name bundle pkg ->
      Cont streamWindow sealRow realWindow ->
        PkgSig bundle realWindow pkg ->
          UnaryHistory ratSeed ∧ UnaryHistory streamWindow ∧ UnaryHistory sealRow ∧
            UnaryHistory dyadicLedger ∧ UnaryHistory realWindow ∧
              Cont ratSeed streamWindow sealRow ∧ Cont streamWindow dyadicLedger realWindow ∧
                Cont streamWindow sealRow realWindow ∧ PkgSig bundle name pkg ∧
                  PkgSig bundle realWindow pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro packet streamSealReal realWindowPkg
  obtain ⟨ratUnary, streamUnary, sealUnary, dyadicUnary, realUnary, _transportUnary,
    _routesUnary, _provenanceUnary, _nameUnary, ratStreamSeal, streamDyadicReal,
    _realTransportRoutes, _routesProvenanceName, namePkg⟩ := packet
  exact
    ⟨ratUnary, streamUnary, sealUnary, dyadicUnary, realUnary, ratStreamSeal,
      streamDyadicReal, streamSealReal, namePkg, realWindowPkg⟩

end BEDC.Derived.StationaryDiagonalWindowRouteUp
