import BEDC.Derived.GaloisGroupUp

namespace BEDC.Derived.GaloisGroupUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem GaloisGroupAutomorphismActionPacket_associative_action_row [AskSetup]
    {sigBundle : ProbeBundle ProbeName} {x y z xy yz left right witness : BHist}
    (policy : AskPolicy (fun h : BHist => UnaryHistory h))
    (total : SigTotalOn sigBundle (fun h : BHist => UnaryHistory h)) :
    UnaryHistory x ->
      UnaryHistory y ->
        UnaryHistory z ->
          Cont x y xy ->
            Cont xy z left ->
              Cont y z yz ->
                Cont x yz right ->
                  Cont left right witness ->
                    SameSig sigBundle left right ∧ hsame left right ∧ UnaryHistory witness ∧
                      hsame witness (append left right) := by
  intro xUnary yUnary zUnary xyCont leftCont yzCont rightCont witnessCont
  have ledgerRows :=
    GaloisGroupAutomorphismActionPacket_associative_composition_ledger
      (sigBundle := sigBundle) policy total xUnary yUnary zUnary xyCont leftCont yzCont
      rightCont
  have xyUnary : UnaryHistory xy :=
    unary_cont_closed xUnary yUnary xyCont
  have yzUnary : UnaryHistory yz :=
    unary_cont_closed yUnary zUnary yzCont
  have leftUnary : UnaryHistory left :=
    unary_cont_closed xyUnary zUnary leftCont
  have rightUnary : UnaryHistory right :=
    unary_cont_closed xUnary yzUnary rightCont
  have witnessUnary : UnaryHistory witness :=
    unary_cont_closed leftUnary rightUnary witnessCont
  exact And.intro ledgerRows.left
    (And.intro ledgerRows.right
      (And.intro witnessUnary witnessCont))

theorem GaloisGroupAutomorphismActionPacket_composition_associativity_public_surface
    [AskSetup] [PackageSetup]
    {sigBundle : ProbeBundle ProbeName}
    {galoisExt group fixedBase action composition inverse classifier provenance ledger endpoint
      x y z xy yz left right : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg}
    (policy : AskPolicy (fun h : BHist => UnaryHistory h))
    (total : SigTotalOn sigBundle (fun h : BHist => UnaryHistory h)) :
    GaloisGroupAutomorphismActionPacket galoisExt group fixedBase action composition inverse
        classifier provenance ledger endpoint bundle pkg ->
      UnaryHistory x ->
        UnaryHistory y ->
          UnaryHistory z ->
            Cont x y xy ->
              Cont xy z left ->
                Cont y z yz ->
                  Cont x yz right ->
                    SameSig sigBundle left right ∧ hsame left right ∧
                      hsame endpoint (append provenance ledger) ∧ PkgSig bundle endpoint pkg := by
  intro packet xUnary yUnary zUnary xyCont leftCont yzCont rightCont
  have ledgerRows :=
    GaloisGroupAutomorphismActionPacket_associative_composition_ledger
      (sigBundle := sigBundle) policy total xUnary yUnary zUnary xyCont leftCont yzCont
      rightCont
  have packetRows :=
    GaloisGroupAutomorphismActionPacket_fixed_base_carrier_obligation packet
  exact And.intro ledgerRows.left
    (And.intro ledgerRows.right
      (And.intro packetRows.right.right.right.right.right.right.right.left
        packetRows.right.right.right.right.right.right.right.right))

end BEDC.Derived.GaloisGroupUp
