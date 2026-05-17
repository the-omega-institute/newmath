import BEDC.Derived.LocatedRealUp

namespace BEDC.Derived.LocatedRealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocatedRealCarrierSurface_scope_real_seal_consumer [AskSetup] [PackageSetup]
    {regseq interval schedule classifier pkgrow sealRow consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedRealCarrierSurface regseq interval schedule classifier pkgrow bundle pkg →
      Cont pkgrow schedule sealRow →
        Cont sealRow classifier consumer →
          PkgSig bundle consumer pkg →
            UnaryHistory regseq ∧ UnaryHistory schedule ∧ UnaryHistory interval ∧
              UnaryHistory classifier ∧ UnaryHistory sealRow ∧ UnaryHistory consumer ∧
                Cont regseq schedule classifier ∧ Cont interval classifier pkgrow ∧
                  Cont pkgrow schedule sealRow ∧ Cont sealRow classifier consumer ∧
                    hsame classifier (append regseq schedule) ∧
                      hsame pkgrow (append interval classifier) ∧
                        hsame sealRow (append pkgrow schedule) ∧
                          hsame consumer (append sealRow classifier) ∧
                            PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame
  intro surface sealCont consumerCont consumerSig
  obtain ⟨regseqUnary, intervalUnary, scheduleUnary, classifierUnary, pkgrowUnary,
    classifierCont, pkgrowCont, _surfaceSig⟩ := surface
  have sealUnary : UnaryHistory sealRow :=
    unary_cont_closed pkgrowUnary scheduleUnary sealCont
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed sealUnary classifierUnary consumerCont
  have classifierSame : hsame classifier (append regseq schedule) :=
    classifierCont
  have pkgrowSame : hsame pkgrow (append interval classifier) :=
    pkgrowCont
  have sealSame : hsame sealRow (append pkgrow schedule) :=
    sealCont
  have consumerSame : hsame consumer (append sealRow classifier) :=
    consumerCont
  exact
    ⟨regseqUnary, scheduleUnary, intervalUnary, classifierUnary, sealUnary, consumerUnary,
      classifierCont, pkgrowCont, sealCont, consumerCont, classifierSame, pkgrowSame, sealSame,
      consumerSame, consumerSig⟩

end BEDC.Derived.LocatedRealUp
