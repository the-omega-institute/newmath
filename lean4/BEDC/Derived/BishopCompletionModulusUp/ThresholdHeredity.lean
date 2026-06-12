import BEDC.Derived.BishopCompletionModulusUp.TasteGate

namespace BEDC.Derived.BishopCompletionModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BishopCompletionModulusCarrier_threshold_heredity [AskSetup] [PackageSetup]
    {M S n k W D R E H C P N successorK successorW successorR successorSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BishopCompletionModulusCarrier M S n k W D R E H C P N bundle pkg ->
      Cont M n successorK ->
        Cont S successorK successorW ->
          Cont successorW D successorR ->
            Cont successorR E successorSeal ->
              SemanticNameCert
                  (fun row : BHist => hsame row successorSeal ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row M ∨ hsame row S ∨ hsame row n ∨ hsame row k ∨
                      hsame row successorK ∨ hsame row successorW ∨
                        hsame row successorR ∨ hsame row successorSeal)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont M n successorK ∧
                      Cont S successorK successorW ∧ Cont successorW D successorR ∧
                        Cont successorR E successorSeal ∧ PkgSig bundle P pkg)
                  hsame ∧
                hsame successorK k ∧ hsame successorR R ∧ hsame successorSeal H := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier successorModulusRoute successorWindowRoute successorRegularRoute
    successorSealRoute
  obtain ⟨unaryM, unaryS, unaryN, _unaryK, _unaryW, unaryD, _unaryR, unaryE,
    _unaryH, _unaryC, _unaryP, _unaryLocalName, modulusRoute, windowRoute,
      regularRoute, sealRoute, provenancePkg, _localNamePkg⟩ := carrier
  have successorKUnary : UnaryHistory successorK :=
    unary_cont_closed unaryM unaryN successorModulusRoute
  have sameSuccessorK : hsame successorK k :=
    cont_respects_hsame (hsame_refl M) (hsame_refl n) successorModulusRoute
      modulusRoute
  have successorWUnary : UnaryHistory successorW :=
    unary_cont_closed unaryS successorKUnary successorWindowRoute
  have sameSuccessorW : hsame successorW W :=
    cont_respects_hsame (hsame_refl S) sameSuccessorK successorWindowRoute
      windowRoute
  have successorRUnary : UnaryHistory successorR :=
    unary_cont_closed successorWUnary unaryD successorRegularRoute
  have sameSuccessorR : hsame successorR R :=
    cont_respects_hsame sameSuccessorW (hsame_refl D) successorRegularRoute
      regularRoute
  have successorSealUnary : UnaryHistory successorSeal :=
    unary_cont_closed successorRUnary unaryE successorSealRoute
  have sameSuccessorSeal : hsame successorSeal H :=
    cont_respects_hsame sameSuccessorR (hsame_refl E) successorSealRoute sealRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row successorSeal ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row M ∨ hsame row S ∨ hsame row n ∨ hsame row k ∨
            hsame row successorK ∨ hsame row successorW ∨ hsame row successorR ∨
              hsame row successorSeal)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont M n successorK ∧ Cont S successorK successorW ∧
            Cont successorW D successorR ∧ Cont successorR E successorSeal ∧
              PkgSig bundle P pkg)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro successorSeal ⟨hsame_refl successorSeal, successorSealUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, successorModulusRoute, successorWindowRoute,
          successorRegularRoute, successorSealRoute, provenancePkg⟩
  }
  exact ⟨cert, sameSuccessorK, sameSuccessorR, sameSuccessorSeal⟩

end BEDC.Derived.BishopCompletionModulusUp
