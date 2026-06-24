import BEDC.Derived.CauchyCompletionOperatorUp.TasteGate
import BEDC.Derived.CauchyCompletionOperatorUp.SeparatedLimitFactorization
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.CauchyCompletionOperatorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

def CauchyCompletionOperatorPacket [AskSetup] [PackageSetup]
    (metric boundary uniform windows readback dyadic separated realSeal transport replay
      provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  hsame localName realSeal ∧
    Cont metric uniform boundary ∧
      Cont boundary windows readback ∧
        Cont readback dyadic separated ∧
          Cont separated realSeal transport ∧
            PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg

theorem CauchyCompletionOperator_namecert_obligation_surface [AskSetup] [PackageSetup]
    {metric boundary uniform windows readback dyadic separated realSeal transport replay
      provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionOperatorPacket metric boundary uniform windows readback dyadic separated
        realSeal transport replay provenance localName bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            hsame row localName ∧
              CauchyCompletionOperatorPacket metric boundary uniform windows readback dyadic
                separated realSeal transport replay provenance localName bundle pkg)
          (fun row : BHist =>
            hsame row metric ∨ hsame row boundary ∨ hsame row uniform ∨
              hsame row windows ∨ hsame row readback ∨ hsame row dyadic ∨
                hsame row separated ∨ hsame row realSeal ∨ hsame row localName)
          (fun row : BHist =>
            hsame row localName ∧ Cont metric uniform boundary ∧
              Cont boundary windows readback ∧ Cont readback dyadic separated ∧
                Cont separated realSeal transport ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle localName pkg)
          hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro packet
  obtain
    ⟨localRealSeal, metricUniformBoundary, boundaryWindowsReadback,
      readbackDyadicSeparated, separatedRealSealTransport, provenancePackage,
      localPackage⟩ := packet
  have packetAtLocalName :
      hsame localName localName ∧
        CauchyCompletionOperatorPacket metric boundary uniform windows readback dyadic
          separated realSeal transport replay provenance localName bundle pkg := by
    exact
      ⟨hsame_refl localName, localRealSeal, metricUniformBoundary,
        boundaryWindowsReadback, readbackDyadicSeparated, separatedRealSealTransport,
        provenancePackage, localPackage⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro localName packetAtLocalName
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
          ⟨hsame_trans (hsame_symm sameRows) source.left, localRealSeal,
            metricUniformBoundary, boundaryWindowsReadback, readbackDyadicSeparated,
            separatedRealSealTransport, provenancePackage, localPackage⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.left, metricUniformBoundary, boundaryWindowsReadback,
          readbackDyadicSeparated, separatedRealSealTransport, provenancePackage,
          localPackage⟩
  }

end BEDC.Derived.CauchyCompletionOperatorUp
