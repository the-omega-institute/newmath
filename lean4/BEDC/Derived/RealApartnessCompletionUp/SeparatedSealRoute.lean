import BEDC.Derived.RealApartnessCompletionUp

namespace BEDC.Derived.RealApartnessCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealApartnessCompletionSeparatedSealRoute [AskSetup] [PackageSetup]
    {apartness separation completion stream readback tolerance sealRow transport replay provenance
      localName separatedRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealApartnessCompletionCarrier apartness separation completion stream readback tolerance
        sealRow transport replay provenance localName bundle pkg →
      Cont apartness separation separatedRead →
        Cont separatedRead tolerance sealRead →
          hsame sealRead sealRow →
            PkgSig bundle sealRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row apartness ∨ hsame row separation ∨ hsame row completion ∨
                      hsame row tolerance ∨ hsame row sealRow ∨ hsame row separatedRead ∨
                        hsame row sealRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont apartness separation separatedRead ∧
                      Cont separatedRead tolerance sealRead ∧ PkgSig bundle sealRead pkg)
                  hsame ∧
                UnaryHistory separatedRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: RealApartnessCompletionCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier separatedRoute sealRoute _sameSeal sealPkg
  obtain ⟨apartnessUnary, separationUnary, _completionUnary, _streamUnary, _readbackUnary,
    toleranceUnary, _sealUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _apartnessSeparationCompletion, _streamReadbackTolerance,
    _toleranceSealReplay, _transportReplayProvenance, _provenancePkg, _localNamePkg⟩ :=
      carrier
  have separatedUnary : UnaryHistory separatedRead :=
    unary_cont_closed apartnessUnary separationUnary separatedRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed separatedUnary toleranceUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row apartness ∨ hsame row separation ∨ hsame row completion ∨
              hsame row tolerance ∨ hsame row sealRow ∨ hsame row separatedRead ∨
                hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont apartness separation separatedRead ∧
              Cont separatedRead tolerance sealRead ∧ PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealReadUnary⟩
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
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, separatedRoute, sealRoute, sealPkg⟩
  }
  exact ⟨cert, separatedUnary, sealReadUnary⟩

end BEDC.Derived.RealApartnessCompletionUp
