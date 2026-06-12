import BEDC.Derived.RealApartnessCompletionUp.ApartnessCauchyWindow

namespace BEDC.Derived.RealApartnessCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealApartnessCompletionSeparatedSealDeterminacy [AskSetup] [PackageSetup]
    {apartness separation completion stream readback tolerance sealRow transport replay
      provenance localName sealLeft sealRight : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealApartnessCompletionApartnessCauchyWindow apartness separation completion stream readback
        tolerance sealRow transport replay provenance localName bundle pkg →
      Cont readback tolerance sealLeft →
        Cont readback tolerance sealRight →
          PkgSig bundle sealLeft pkg →
            PkgSig bundle sealRight pkg →
              hsame sealLeft sealRight ∧
                SemanticNameCert
                    (fun row : BHist => hsame row sealLeft ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row readback ∨ hsame row tolerance ∨ hsame row sealLeft ∨
                        hsame row sealRight)
                    (fun row : BHist =>
                      UnaryHistory row ∧ PkgSig bundle sealLeft pkg ∧
                        PkgSig bundle sealRight pkg)
                    hsame := by
  -- BEDC touchpoint anchor: RealApartnessCompletionApartnessCauchyWindow BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro window leftRoute rightRoute leftPkg rightPkg
  obtain ⟨carrier, _apartnessCompletion, _completionReadback, _readbackTolerance,
    _provenancePkg, _localNamePkg⟩ := window
  obtain ⟨_apartnessUnary, _separationUnary, _completionUnary, _streamUnary,
    readbackUnary, toleranceUnary, _sealUnary, _transportUnary, _replayUnary,
    _provenanceUnary, _localNameUnary, _apartnessSeparationCompletion,
    _streamReadbackTolerance, _toleranceSealReplay, _transportReplayProvenance,
    _carrierProvenancePkg, _carrierLocalNamePkg⟩ := carrier
  have sameSeal : hsame sealLeft sealRight :=
    cont_deterministic leftRoute rightRoute
  have leftUnary : UnaryHistory sealLeft :=
    unary_cont_closed readbackUnary toleranceUnary leftRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealLeft ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row readback ∨ hsame row tolerance ∨ hsame row sealLeft ∨
              hsame row sealRight)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle sealLeft pkg ∧ PkgSig bundle sealRight pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealLeft ⟨hsame_refl sealLeft, leftUnary⟩
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
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inl source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, leftPkg, rightPkg⟩
  }
  exact ⟨sameSeal, cert⟩

end BEDC.Derived.RealApartnessCompletionUp
