import BEDC.Derived.CauchyEquivalenceSetoidUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CauchyEquivalenceSetoidUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyEquivalenceSetoidCompletionTailComposition [AskSetup] [PackageSetup]
    {S0 S1 R0 R1 D T E H C P N classifierRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyEquivalenceSetoidCarrier S0 S1 R0 R1 D T E H C P N bundle pkg ->
      Cont T E classifierRead ->
        Cont classifierRead N completionRead ->
          PkgSig bundle completionRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row S0 ∨ hsame row S1 ∨ hsame row R0 ∨ hsame row R1 ∨
                    hsame row D ∨ hsame row T ∨ hsame row E ∨ hsame row H ∨
                      hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row completionRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont T E classifierRead ∧
                    Cont classifierRead N completionRead ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle N pkg ∧ PkgSig bundle completionRead pkg)
                hsame ∧ UnaryHistory classifierRead ∧ UnaryHistory completionRead := by
  -- BEDC touchpoint anchor: CauchyEquivalenceSetoidCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrierRows classifierRoute completionRoute completionPkg
  obtain ⟨_s0Unary, _s1Unary, _r0Unary, _r1Unary, _dUnary, testUnary, sealUnary,
    _transportUnary, _replayUnary, provenanceUnary, nameUnary, _leftTransport,
    _rightReplay, _dyadicSeal, provenancePkg, namePkg⟩ := carrierRows
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed testUnary sealUnary classifierRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed classifierUnary nameUnary completionRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S0 ∨ hsame row S1 ∨ hsame row R0 ∨ hsame row R1 ∨
              hsame row D ∨ hsame row T ∨ hsame row E ∨ hsame row H ∨ hsame row C ∨
                hsame row P ∨ hsame row N ∨ hsame row completionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont T E classifierRead ∧
              Cont classifierRead N completionRead ∧ PkgSig bundle P pkg ∧
                PkgSig bundle N pkg ∧ PkgSig bundle completionRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro completionRead ⟨hsame_refl completionRead, completionUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      exact sourceRow.left
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, classifierRoute, completionRoute, provenancePkg, namePkg,
          completionPkg⟩
  }
  exact ⟨cert, classifierUnary, completionUnary⟩

end BEDC.Derived.CauchyEquivalenceSetoidUp
