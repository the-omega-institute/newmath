import BEDC.Derived.CauchyfiltercompletionUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CauchyfiltercompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyFilterCompletionPacket_filterbase_admission [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name
      admitted completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      Cont filter windows admitted →
        Cont admitted readback completionRead →
          PkgSig bundle completionRead pkg →
            SemanticNameCert
                (fun row : BHist =>
                  (hsame row admitted ∨ hsame row completionRead) ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row filter ∨ hsame row windows ∨ hsame row admitted ∨
                    hsame row readback ∨ hsame row completionRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle completionRead pkg ∧
                    Cont admitted readback completionRead)
                hsame ∧
              UnaryHistory admitted ∧ UnaryHistory completionRead ∧
                Cont filter windows tolerance ∧ Cont tolerance readback sealRow ∧
                  PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig SemanticNameCert
  intro packet filterWindowsAdmitted admittedReadbackCompletion completionPkg
  obtain ⟨filterUnary, windowsUnary, _toleranceUnary, readbackUnary, _sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, filterWindowsTolerance,
    toleranceReadbackSeal, _transportReplayProvenance, provenancePkg, _namePkg⟩ := packet
  have admittedUnary : UnaryHistory admitted :=
    unary_cont_closed filterUnary windowsUnary filterWindowsAdmitted
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed admittedUnary readbackUnary admittedReadbackCompletion
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row admitted ∨ hsame row completionRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row filter ∨ hsame row windows ∨ hsame row admitted ∨
              hsame row readback ∨ hsame row completionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle completionRead pkg ∧
              Cont admitted readback completionRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro admitted ⟨Or.inl (hsame_refl admitted), admittedUnary⟩
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
        cases source with
        | intro sourceRows sourceUnary =>
            constructor
            · cases sourceRows with
              | inl sameAdmitted =>
                  exact Or.inl (hsame_trans (hsame_symm sameRows) sameAdmitted)
              | inr sameCompletion =>
                  exact Or.inr (hsame_trans (hsame_symm sameRows) sameCompletion)
            · exact unary_transport sourceUnary sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameAdmitted =>
          exact Or.inr (Or.inr (Or.inl sameAdmitted))
      | inr sameCompletion =>
          exact Or.inr (Or.inr (Or.inr (Or.inr sameCompletion)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, completionPkg, admittedReadbackCompletion⟩
  }
  exact
    ⟨cert, admittedUnary, completionUnary, filterWindowsTolerance, toleranceReadbackSeal,
      provenancePkg⟩

end BEDC.Derived.CauchyfiltercompletionUp
