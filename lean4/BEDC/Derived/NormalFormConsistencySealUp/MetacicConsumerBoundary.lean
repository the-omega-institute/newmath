import BEDC.Derived.NormalFormConsistencySealUp.CriticalPairRoute

namespace BEDC.Derived.NormalFormConsistencySealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem NormalFormConsistencySealMetacicConsumerBoundary [AskSetup] [PackageSetup]
    {T F N K X H C P L closedRead socketRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    normalFormConsistencySealFields (NormalFormConsistencySealUp.mk T F N K X H C P L) =
        [T, F, N, K, X, H, C, P, L] ->
      UnaryHistory T ->
        UnaryHistory F ->
          UnaryHistory N ->
            UnaryHistory K ->
              UnaryHistory C ->
                Cont T F closedRead ->
                  Cont N K socketRead ->
                    Cont socketRead C namedRead ->
                      PkgSig bundle P pkg ->
                        PkgSig bundle L pkg ->
                          SemanticNameCert
                                (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row T ∨ hsame row F ∨ hsame row N ∨ hsame row K ∨
                                    hsame row socketRead ∨ hsame row namedRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont T F closedRead ∧
                                    Cont N K socketRead ∧ Cont socketRead C namedRead ∧
                                      PkgSig bundle P pkg ∧ PkgSig bundle L pkg)
                                hsame ∧
                              UnaryHistory closedRead ∧ UnaryHistory socketRead ∧
                                UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame UnaryHistory
  intro fieldsExact unaryT unaryF unaryN unaryK unaryC closedRoute socketRoute namedRoute
    provenancePkg localNamePkg
  cases fieldsExact
  have closedUnary : UnaryHistory closedRead :=
    unary_cont_closed unaryT unaryF closedRoute
  have socketUnary : UnaryHistory socketRead :=
    unary_cont_closed unaryN unaryK socketRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed socketUnary unaryC namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row F ∨ hsame row N ∨ hsame row K ∨
              hsame row socketRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont T F closedRead ∧ Cont N K socketRead ∧
              Cont socketRead C namedRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle L pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, closedRoute, socketRoute, namedRoute, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, closedUnary, socketUnary, namedUnary⟩

end BEDC.Derived.NormalFormConsistencySealUp
