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

theorem CauchyFilterCompletionRootDataExhaustion [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name rootRead
      completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg ->
      Cont filter readback rootRead ->
        Cont rootRead sealRow completionRead ->
          PkgSig bundle completionRead pkg ->
            SemanticNameCert
                (fun row : BHist =>
                  CauchyFilterCompletionPacket filter windows tolerance readback sealRow
                      transport replay provenance name bundle pkg ∧
                    (hsame row filter ∨ hsame row windows ∨ hsame row tolerance ∨
                      hsame row readback ∨ hsame row sealRow ∨ hsame row rootRead ∨
                        hsame row completionRead))
                (fun _row : BHist =>
                  Cont filter windows tolerance ∧ Cont tolerance readback sealRow ∧
                    Cont filter readback rootRead ∧ Cont rootRead sealRow completionRead ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle completionRead pkg)
                (fun row : BHist =>
                  UnaryHistory row ∧
                    (PkgSig bundle provenance pkg ∨ PkgSig bundle completionRead pkg))
                hsame ∧
              UnaryHistory rootRead ∧ UnaryHistory completionRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame SemanticNameCert
  intro packet rootRoute completionRoute completionPkg
  have packetWhole := packet
  obtain ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, filterWindows,
    toleranceReadback, _transportReplay, provenancePkg, _namePkg⟩ := packet
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed filterUnary readbackUnary rootRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed rootUnary sealUnary completionRoute
  have sourceFilter :
      (fun row : BHist =>
        CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
            provenance name bundle pkg ∧
          (hsame row filter ∨ hsame row windows ∨ hsame row tolerance ∨
            hsame row readback ∨ hsame row sealRow ∨ hsame row rootRead ∨
              hsame row completionRead)) filter := by
    exact ⟨packetWhole, Or.inl (hsame_refl filter)⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport
                replay provenance name bundle pkg ∧
              (hsame row filter ∨ hsame row windows ∨ hsame row tolerance ∨
                hsame row readback ∨ hsame row sealRow ∨ hsame row rootRead ∨
                  hsame row completionRead))
          (fun _row : BHist =>
            Cont filter windows tolerance ∧ Cont tolerance readback sealRow ∧
              Cont filter readback rootRead ∧ Cont rootRead sealRow completionRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle completionRead pkg)
          (fun row : BHist =>
            UnaryHistory row ∧
              (PkgSig bundle provenance pkg ∨ PkgSig bundle completionRead pkg))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro filter sourceFilter
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
        cases sameRows
        exact source
    }
    pattern_sound := by
      intro _row _source
      exact
        ⟨filterWindows, toleranceReadback, rootRoute, completionRoute, provenancePkg,
          completionPkg⟩
    ledger_sound := by
      intro _row source
      cases source with
      | intro _sourcePacket sourceRows =>
          cases sourceRows with
          | inl sameFilter =>
              exact ⟨unary_transport filterUnary (hsame_symm sameFilter),
                Or.inl provenancePkg⟩
          | inr rest =>
              cases rest with
              | inl sameWindows =>
                  exact ⟨unary_transport windowsUnary (hsame_symm sameWindows),
                    Or.inl provenancePkg⟩
              | inr rest =>
                  cases rest with
                  | inl sameTolerance =>
                      exact ⟨unary_transport toleranceUnary (hsame_symm sameTolerance),
                        Or.inl provenancePkg⟩
                  | inr rest =>
                      cases rest with
                      | inl sameReadback =>
                          exact ⟨unary_transport readbackUnary (hsame_symm sameReadback),
                            Or.inl provenancePkg⟩
                      | inr rest =>
                          cases rest with
                          | inl sameSeal =>
                              exact ⟨unary_transport sealUnary (hsame_symm sameSeal),
                                Or.inl provenancePkg⟩
                          | inr rest =>
                              cases rest with
                              | inl sameRoot =>
                                  exact ⟨unary_transport rootUnary (hsame_symm sameRoot),
                                    Or.inr completionPkg⟩
                              | inr sameCompletion =>
                                  exact
                                    ⟨unary_transport completionUnary
                                      (hsame_symm sameCompletion), Or.inr completionPkg⟩
  }
  exact ⟨cert, rootUnary, completionUnary⟩

end BEDC.Derived.CauchyfiltercompletionUp
