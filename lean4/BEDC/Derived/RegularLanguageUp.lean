import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularLanguageUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularLanguageAutomatonPacket [AskSetup] [PackageSetup]
    (alphabet states start accept transition word run endpoint transport route provenance : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory alphabet ∧ UnaryHistory states ∧ UnaryHistory start ∧
    UnaryHistory accept ∧ UnaryHistory transition ∧ UnaryHistory word ∧
      UnaryHistory route ∧ Cont start word run ∧ Cont run accept endpoint ∧
        Cont transition endpoint transport ∧ Cont transport route provenance ∧
          PkgSig bundle provenance pkg

theorem RegularLanguageAutomatonPacket_deterministic_run_ledger [AskSetup] [PackageSetup]
    {alphabet states start accept transition word run endpoint transport route provenance
      run' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularLanguageAutomatonPacket alphabet states start accept transition word run endpoint
        transport route provenance bundle pkg ->
      Cont start word run' ->
        UnaryHistory start ∧ UnaryHistory word ∧ UnaryHistory run' ∧ hsame run run' ∧
          Cont start word run' ∧ PkgSig bundle provenance pkg := by
  intro packet runRow'
  have startUnary : UnaryHistory start :=
    packet.right.right.left
  have wordUnary : UnaryHistory word :=
    packet.right.right.right.right.right.left
  have runRow : Cont start word run :=
    packet.right.right.right.right.right.right.right.left
  have sameRun : hsame run run' :=
    cont_respects_hsame (hsame_refl start) (hsame_refl word) runRow runRow'
  have runUnary' : UnaryHistory run' :=
    unary_cont_closed startUnary wordUnary runRow'
  have pkgSig : PkgSig bundle provenance pkg :=
    packet.right.right.right.right.right.right.right.right.right.right.right
  exact
    ⟨startUnary, wordUnary, runUnary', sameRun, runRow', pkgSig⟩

theorem RegularLanguageAutomatonPacket_classified_word_transport [AskSetup] [PackageSetup]
    {alphabet states start accept transition word run endpoint transport route provenance run'
      accept' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularLanguageAutomatonPacket alphabet states start accept transition word run endpoint
        transport route provenance bundle pkg ->
      hsame run run' ->
        hsame accept accept' ->
          Cont run' accept' endpoint' ->
            UnaryHistory run' ∧ UnaryHistory accept' ∧ UnaryHistory endpoint' ∧
              hsame endpoint endpoint' ∧ Cont run' accept' endpoint' ∧
                PkgSig bundle provenance pkg := by
  intro packet sameRun sameAccept endpointRow'
  have startUnary : UnaryHistory start :=
    packet.right.right.left
  have acceptUnary : UnaryHistory accept :=
    packet.right.right.right.left
  have wordUnary : UnaryHistory word :=
    packet.right.right.right.right.right.left
  have runRow : Cont start word run :=
    packet.right.right.right.right.right.right.right.left
  have endpointRow : Cont run accept endpoint :=
    packet.right.right.right.right.right.right.right.right.left
  have runUnary : UnaryHistory run :=
    unary_cont_closed startUnary wordUnary runRow
  have runUnary' : UnaryHistory run' :=
    unary_transport runUnary sameRun
  have acceptUnary' : UnaryHistory accept' :=
    unary_transport acceptUnary sameAccept
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed runUnary' acceptUnary' endpointRow'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameRun sameAccept endpointRow endpointRow'
  have pkgSig : PkgSig bundle provenance pkg :=
    packet.right.right.right.right.right.right.right.right.right.right.right
  exact
    ⟨runUnary', acceptUnary', endpointUnary', sameEndpoint, endpointRow', pkgSig⟩

end BEDC.Derived.RegularLanguageUp
