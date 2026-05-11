import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BraidGroupUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BraidGroupArtinPacket [AskSetup] [PackageSetup]
    (strand word ledger classifier provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory strand ∧ UnaryHistory word ∧ UnaryHistory ledger ∧
    Cont word ledger classifier ∧ Cont classifier provenance endpoint ∧
      PkgSig bundle endpoint pkg

theorem BraidGroupArtinPacket_artin_ledger_stability [AskSetup] [PackageSetup]
    {strand word ledger classifier provenance endpoint strand' word' ledger' classifier'
      provenance' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BraidGroupArtinPacket strand word ledger classifier provenance endpoint bundle pkg ->
      hsame strand strand' -> hsame word word' -> hsame ledger ledger' ->
        hsame provenance provenance' -> Cont word' ledger' classifier' ->
          Cont classifier' provenance' endpoint' -> PkgSig bundle endpoint' pkg ->
            BraidGroupArtinPacket strand' word' ledger' classifier' provenance' endpoint'
                bundle pkg ∧
              hsame classifier classifier' ∧ hsame endpoint endpoint' := by
  intro packet sameStrand sameWord sameLedger sameProvenance classifierRow'
  intro endpointRow' pkgSig'
  have classifierSame : hsame classifier classifier' :=
    cont_respects_hsame sameWord sameLedger packet.right.right.right.left classifierRow'
  have endpointSame : hsame endpoint endpoint' :=
    cont_respects_hsame classifierSame sameProvenance packet.right.right.right.right.left
      endpointRow'
  have packet' :
      BraidGroupArtinPacket strand' word' ledger' classifier' provenance' endpoint'
          bundle pkg :=
    ⟨unary_transport packet.left sameStrand,
      unary_transport packet.right.left sameWord,
      unary_transport packet.right.right.left sameLedger,
      classifierRow',
      endpointRow',
      pkgSig'⟩
  exact ⟨packet', classifierSame, endpointSame⟩

end BEDC.Derived.BraidGroupUp
