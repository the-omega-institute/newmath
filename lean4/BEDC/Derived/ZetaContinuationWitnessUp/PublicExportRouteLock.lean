import BEDC.Derived.ZetaContinuationWitnessUp
import BEDC.FKernel.Cont.Cancellation

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationWitnessPacket_public_export_route_lock [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name
      publicRead publicRead' hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports
        routes provenance name bundle pkg →
      UnaryHistory routes →
        UnaryHistory name →
          Cont routes name publicRead →
            Cont routes name publicRead' →
              PkgSig bundle publicRead pkg →
                PkgSig bundle publicRead' pkg →
                  hsame publicRead publicRead' ∧ UnaryHistory publicRead ∧
                    UnaryHistory publicRead' ∧ hsame publicRead (append routes name) ∧
                      hsame publicRead' (append routes name) ∧ PkgSig bundle name pkg ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle publicRead pkg ∧
                          PkgSig bundle publicRead' pkg ∧
                            (Cont publicRead (BHist.e0 hostTail) routes → False) ∧
                              (Cont publicRead (BHist.e1 hostTail) routes → False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet routesUnary nameUnary publicRoute publicRoute' publicPkg publicPkg'
  obtain ⟨_basicAnalytic, _analyticTransport, _poleGamma, _transportProvenance, namePkg,
    provenancePkg⟩ := packet
  have publicSame : hsame publicRead publicRead' :=
    cont_respects_hsame (hsame_refl routes) (hsame_refl name) publicRoute publicRoute'
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed routesUnary nameUnary publicRoute
  have publicUnary' : UnaryHistory publicRead' :=
    unary_cont_closed routesUnary nameUnary publicRoute'
  exact
    ⟨publicSame, publicUnary, publicUnary', publicRoute, publicRoute', namePkg,
      provenancePkg, publicPkg, publicPkg',
      (fun hostReturn =>
        cont_mutual_extension_right_tail_absurd.left publicRoute hostReturn),
      (fun hostReturn =>
        cont_mutual_extension_right_tail_absurd.right publicRoute hostReturn)⟩

end BEDC.Derived.ZetaContinuationWitnessUp
