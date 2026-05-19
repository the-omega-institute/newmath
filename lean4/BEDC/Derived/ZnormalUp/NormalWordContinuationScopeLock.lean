import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_normal_word_continuation_scope_lock [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name terminalRead
      siblingRead joined : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg ->
      Cont typed fuel terminalRead ->
        Cont normal continuation siblingRead ->
          Cont terminalRead siblingRead joined ->
            PkgSig bundle siblingRead pkg ->
              PkgSig bundle joined pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row joined ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row terminalRead ∨ hsame row siblingRead ∨ hsame row joined)
                    (fun row : BHist => hsame row joined ∧ PkgSig bundle joined pkg)
                    hsame ∧
                  hsame terminalRead terminal ∧ UnaryHistory siblingRead ∧
                    UnaryHistory joined ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet typedFuelTerminalRead normalContinuationSibling terminalSiblingJoined
    _siblingReadPkg joinedPkg
  obtain ⟨typedUnary, fuelUnary, _terminalUnary, normalUnary, continuationUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have terminalReadSame : hsame terminalRead terminal :=
    cont_deterministic typedFuelTerminalRead typedFuelTerminal
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelTerminalRead
  have siblingReadUnary : UnaryHistory siblingRead :=
    unary_cont_closed normalUnary continuationUnary normalContinuationSibling
  have joinedUnary : UnaryHistory joined :=
    unary_cont_closed terminalReadUnary siblingReadUnary terminalSiblingJoined
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row joined ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row terminalRead ∨ hsame row siblingRead ∨ hsame row joined)
          (fun row : BHist => hsame row joined ∧ PkgSig bundle joined pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro joined ⟨hsame_refl joined, joinedUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr source.left)
    ledger_sound := by
      intro _row source
      exact ⟨source.left, joinedPkg⟩
  }
  exact ⟨cert, terminalReadSame, siblingReadUnary, joinedUnary, provenancePkg⟩

end BEDC.Derived.ZnormalUp
