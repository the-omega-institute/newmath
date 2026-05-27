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

theorem AuthorizedGeneratorRecursorL10PublicSourceHandoff [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N sourceRead streamRead regseqRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont O N sourceRead ->
        Cont sourceRead C streamRead ->
          Cont streamRead G regseqRead ->
            Cont regseqRead N realRead ->
              PkgSig bundle realRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row I ∨ hsame row E ∨ hsame row M ∨ hsame row B ∨
                        hsame row D ∨ hsame row O ∨ hsame row A ∨ hsame row H ∨
                          hsame row C ∨ hsame row P ∨ hsame row G ∨ hsame row N ∨
                            hsame row sourceRead ∨ hsame row streamRead ∨
                              hsame row regseqRead ∨ hsame row realRead)
                    (fun row : BHist => PkgSig bundle realRead pkg ∧ hsame row realRead)
                    hsame ∧
                  UnaryHistory sourceRead ∧ UnaryHistory streamRead ∧
                    UnaryHistory regseqRead ∧ UnaryHistory realRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame
  intro carrier sourceRoute streamRoute regseqRoute realRoute realPkg
  rcases carrier with
    ⟨_unaryI, _unaryE, _unaryM, _unaryB, _unaryD, unaryO, _unaryA, _unaryH,
      unaryC, _provenancePkg, unaryG, unaryN, _signatureEliminatorMotive,
      _motiveBranchDescent, _descentOutputAudit, _transportSame, _pkgProvenance⟩
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed unaryO unaryN sourceRoute
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed sourceUnary unaryC streamRoute
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed streamUnary unaryG regseqRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed regseqUnary unaryN realRoute
  have sourceReal :
      (fun row : BHist => hsame row realRead ∧ UnaryHistory row) realRead := by
    exact ⟨hsame_refl realRead, realUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row I ∨ hsame row E ∨ hsame row M ∨ hsame row B ∨ hsame row D ∨
              hsame row O ∨ hsame row A ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row G ∨ hsame row N ∨ hsame row sourceRead ∨
                  hsame row streamRead ∨ hsame row regseqRead ∨ hsame row realRead)
          (fun row : BHist => PkgSig bundle realRead pkg ∧ hsame row realRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro realRead sourceReal
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
        exact
          Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr source.left))))))))))))))
      ledger_sound := by
        intro _row source
        exact ⟨realPkg, source.left⟩
    }
  exact ⟨cert, sourceUnary, streamUnary, regseqUnary, realUnary⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
