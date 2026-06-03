import BEDC.Derived.RepresentedSpaceUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.RepresentedSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RepresentedSpaceCarrier_root_real_seal_obligations [AskSetup] [PackageSetup]
    {name schedule relation target transport replay provenance localName targetRead sealRead
      finalSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg}
    (carrier : BEDC.Derived.RepresentedSpaceUp name schedule relation target transport replay
      provenance localName bundle pkg)
    (relationTargetRoute : Cont relation target targetRead)
    (targetSealRoute : Cont targetRead provenance sealRead)
    (sealReplayRoute : Cont sealRead replay finalSeal)
    (finalPkg : PkgSig bundle finalSeal pkg) :
    SemanticNameCert
        (fun row : BHist => hsame row finalSeal ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row name ∨ hsame row schedule ∨ hsame row relation ∨ hsame row target ∨
            hsame row targetRead ∨ hsame row sealRead ∨ hsame row finalSeal)
        (fun row : BHist =>
          hsame row finalSeal ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle finalSeal pkg)
        hsame ∧
      UnaryHistory targetRead ∧ UnaryHistory sealRead ∧ UnaryHistory finalSeal ∧
        PkgSig bundle provenance pkg ∧ PkgSig bundle finalSeal pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  obtain ⟨_nameUnary, _scheduleUnary, relationUnary, targetUnary, _transportUnary,
    replayUnary, provenanceUnary, _localNameUnary, _nameScheduleReplay,
    _relationTargetTransport, _localNameTransport, provenancePkg⟩ := carrier
  have targetReadUnary : UnaryHistory targetRead :=
    unary_cont_closed relationUnary targetUnary relationTargetRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed targetReadUnary provenanceUnary targetSealRoute
  have finalSealUnary : UnaryHistory finalSeal :=
    unary_cont_closed sealReadUnary replayUnary sealReplayRoute
  have sourceFinalSeal :
      (fun row : BHist => hsame row finalSeal ∧ UnaryHistory row) finalSeal := by
    exact ⟨hsame_refl finalSeal, finalSealUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row finalSeal ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row name ∨ hsame row schedule ∨ hsame row relation ∨ hsame row target ∨
              hsame row targetRead ∨ hsame row sealRead ∨ hsame row finalSeal)
          (fun row : BHist =>
            hsame row finalSeal ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle finalSeal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro finalSeal sourceFinalSeal
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, provenancePkg, finalPkg⟩
  }
  exact ⟨cert, targetReadUnary, sealReadUnary, finalSealUnary, provenancePkg, finalPkg⟩

end BEDC.Derived.RepresentedSpaceUp
