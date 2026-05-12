import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyCompletionFunctorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyCompletionFunctorPacket [AskSetup] [PackageSetup]
    (metric regular «seal» «monad» universal classifier transport nameCert endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory metric ∧ UnaryHistory regular ∧ UnaryHistory «seal» ∧ UnaryHistory «monad» ∧
    UnaryHistory universal ∧ UnaryHistory classifier ∧ UnaryHistory transport ∧
      UnaryHistory nameCert ∧ UnaryHistory endpoint ∧ Cont metric regular «seal» ∧
        Cont «monad» universal endpoint ∧ Cont classifier transport nameCert ∧
          PkgSig bundle endpoint pkg

theorem CauchyCompletionFunctorPacket_namecert_obligations [AskSetup] [PackageSetup]
    {metric regular «seal» «monad» universal classifier transport nameCert endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionFunctorPacket metric regular «seal» «monad» universal classifier transport nameCert
        endpoint bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            hsame row endpoint ∧
              CauchyCompletionFunctorPacket metric regular «seal» «monad» universal classifier transport
                nameCert endpoint bundle pkg)
          (fun row : BHist => hsame row endpoint)
          (fun row : BHist => hsame row endpoint ∧ PkgSig bundle endpoint pkg)
          hsame ∧
        UnaryHistory metric ∧ UnaryHistory regular ∧ UnaryHistory «seal» ∧ UnaryHistory «monad» ∧
          UnaryHistory universal ∧ Cont metric regular «seal» ∧ Cont «monad» universal endpoint ∧
            PkgSig bundle endpoint pkg := by
  intro packet
  have packetWitness := packet
  obtain ⟨metricUnary, regularUnary, sealUnary, monadUnary, universalUnary, _classifierUnary,
    _transportUnary, _nameCertUnary, _endpointUnary, metricRegularSeal, monadUniversalEndpoint,
    _classifierTransportNameCert, endpointPkg⟩ := packet
  have sourceEndpoint :
      (fun row : BHist =>
        hsame row endpoint ∧
          CauchyCompletionFunctorPacket metric regular «seal» «monad» universal classifier transport
            nameCert endpoint bundle pkg) endpoint := by
    exact ⟨hsame_refl endpoint, packetWitness⟩
  have core :
      NameCert
        (fun row : BHist =>
          hsame row endpoint ∧
            CauchyCompletionFunctorPacket metric regular «seal» «monad» universal classifier transport
              nameCert endpoint bundle pkg)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro endpoint sourceEndpoint
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _other _third sameRO sameOT
        exact hsame_trans sameRO sameOT
      carrier_respects_equiv := by
        intro _row _other same source
        exact ⟨hsame_trans (hsame_symm same) source.left, source.right⟩
    }
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row endpoint ∧
              CauchyCompletionFunctorPacket metric regular «seal» «monad» universal classifier transport
                nameCert endpoint bundle pkg)
          (fun row : BHist => hsame row endpoint)
          (fun row : BHist => hsame row endpoint ∧ PkgSig bundle endpoint pkg)
          hsame := by
    exact {
      core := core
      pattern_sound := by
        intro _row source
        exact source.left
      ledger_sound := by
        intro _row source
        exact ⟨source.left, endpointPkg⟩
    }
  exact
    ⟨cert, metricUnary, regularUnary, sealUnary, monadUnary, universalUnary, metricRegularSeal,
      monadUniversalEndpoint, endpointPkg⟩

end BEDC.Derived.CauchyCompletionFunctorUp
