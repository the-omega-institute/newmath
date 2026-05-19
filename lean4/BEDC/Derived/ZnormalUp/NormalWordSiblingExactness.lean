import BEDC.Derived.ZnormalUp
import BEDC.FKernel.Cont.Cancellation

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_normal_word_sibling_exactness [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name siblingRead
      hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg ->
      Cont normal continuation siblingRead ->
        PkgSig bundle siblingRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row siblingRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row normal ∨ hsame row continuation ∨ hsame row siblingRead)
              (fun row : BHist =>
                hsame row siblingRead ∧ PkgSig bundle siblingRead pkg ∧
                  (Cont row (BHist.e0 hostTail) normal -> False) ∧
                    (Cont row (BHist.e1 hostTail) continuation -> False))
              hsame ∧
            UnaryHistory normal ∧ UnaryHistory continuation ∧ UnaryHistory siblingRead ∧
              Cont normal continuation siblingRead ∧ PkgSig bundle name pkg ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle siblingRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro packet normalContinuationSibling siblingPkg
  obtain ⟨_typedUnary, _fuelUnary, _terminalUnary, normalUnary, continuationUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, _typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, namePkg, provenancePkg⟩ :=
    packet
  have siblingUnary : UnaryHistory siblingRead :=
    unary_cont_closed normalUnary continuationUnary normalContinuationSibling
  have sourceAtSibling : hsame siblingRead siblingRead ∧ UnaryHistory siblingRead :=
    ⟨hsame_refl siblingRead, siblingUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row siblingRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row normal ∨ hsame row continuation ∨ hsame row siblingRead)
          (fun row : BHist =>
            hsame row siblingRead ∧ PkgSig bundle siblingRead pkg ∧
              (Cont row (BHist.e0 hostTail) normal -> False) ∧
                (Cont row (BHist.e1 hostTail) continuation -> False))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro siblingRead sourceAtSibling
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
        exact
          ⟨hsame_trans (hsame_symm same) source.left,
            unary_transport source.right same⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr source.left)
    ledger_sound := by
      intro row source
      cases source.left
      have e0Refusal : Cont siblingRead (BHist.e0 hostTail) normal -> False :=
        fun back =>
          cont_mutual_extension_right_tail_absurd.left normalContinuationSibling back
      have e1Refusal : Cont siblingRead (BHist.e1 hostTail) continuation -> False :=
        fun back =>
          have flippedSame : hsame siblingRead (append continuation normal) :=
            unary_cont_comm normalUnary continuationUnary normalContinuationSibling (cont_intro rfl)
          have flippedRoute : Cont continuation normal siblingRead :=
            cont_result_hsame_transport (cont_intro rfl) (hsame_symm flippedSame)
          cont_mutual_extension_right_tail_absurd.right flippedRoute back
      exact ⟨hsame_refl siblingRead, siblingPkg, e0Refusal, e1Refusal⟩
  }
  exact
    ⟨cert, normalUnary, continuationUnary, siblingUnary, normalContinuationSibling, namePkg,
      provenancePkg, siblingPkg⟩

end BEDC.Derived.ZnormalUp
