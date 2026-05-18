import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier
import BEDC.FKernel.NameCert

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorClosedSubstitutionSourceExposure [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N branchRead descentRead outputRead boundaryRead sourceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont I E branchRead ->
        Cont branchRead D descentRead ->
          Cont descentRead O outputRead ->
            Cont outputRead G boundaryRead ->
              Cont boundaryRead N sourceRead ->
                PkgSig bundle sourceRead pkg ->
                  SemanticNameCert
                      (fun row : BHist =>
                        hsame row N ∧
                          AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg)
                      (fun row : BHist =>
                        hsame row N ∧ Cont I E branchRead ∧ Cont branchRead D descentRead ∧
                          Cont descentRead O outputRead ∧ Cont outputRead G boundaryRead ∧
                            Cont boundaryRead N sourceRead)
                      (fun row : BHist =>
                        hsame row N ∧ PkgSig bundle P pkg ∧ PkgSig bundle sourceRead pkg)
                      hsame ∧
                    UnaryHistory branchRead ∧ UnaryHistory descentRead ∧
                      UnaryHistory outputRead ∧ UnaryHistory boundaryRead ∧
                        UnaryHistory sourceRead ∧ hsame H (append A C) ∧
                          PkgSig bundle P pkg ∧ PkgSig bundle sourceRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig SemanticNameCert hsame
  intro carrier signatureEliminatorBranch branchDescentRead descentOutputRead
    outputBoundaryRead boundarySourceRead sourcePkg
  have carrierPacket := carrier
  obtain ⟨unaryI, unaryE, _unaryM, _unaryB, unaryD, unaryO, _unaryA, _unaryH, _unaryC,
    provenanceUnary, unaryG, unaryN, _carrierSignature, _carrierDescent,
    _carrierOutput, transportAuditContinuation, provenancePkg⟩ := carrier
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed unaryI unaryE signatureEliminatorBranch
  have descentReadUnary : UnaryHistory descentRead :=
    unary_cont_closed branchReadUnary unaryD branchDescentRead
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed descentReadUnary unaryO descentOutputRead
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed outputReadUnary unaryG outputBoundaryRead
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed boundaryReadUnary unaryN boundarySourceRead
  have sourceN :
      (fun row : BHist =>
        hsame row N ∧ AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg)
        N := by
    exact ⟨hsame_refl N, carrierPacket⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row N ∧ AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg)
          (fun row : BHist =>
            hsame row N ∧ Cont I E branchRead ∧ Cont branchRead D descentRead ∧
              Cont descentRead O outputRead ∧ Cont outputRead G boundaryRead ∧
                Cont boundaryRead N sourceRead)
          (fun row : BHist =>
            hsame row N ∧ PkgSig bundle P pkg ∧ PkgSig bundle sourceRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro N sourceN
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        exact ⟨hsame_trans (hsame_symm same) source.left, source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact
        ⟨source.left, signatureEliminatorBranch, branchDescentRead, descentOutputRead,
          outputBoundaryRead, boundarySourceRead⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, provenancePkg, sourcePkg⟩
  }
  exact
    ⟨cert, branchReadUnary, descentReadUnary, outputReadUnary, boundaryReadUnary,
      sourceReadUnary, transportAuditContinuation, provenancePkg, sourcePkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
