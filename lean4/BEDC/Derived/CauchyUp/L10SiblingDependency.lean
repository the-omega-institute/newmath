import BEDC.Derived.CauchyUp

namespace BEDC.Derived.CauchyUp.L10SiblingDependency

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyL10SiblingDependencyRoute [AskSetup] [PackageSetup]
    {streamWindow regSeqTail dyadicLedger realSeal streamRead regularRead toleranceRead
      publicApprox transport replay provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory streamWindow ->
      UnaryHistory regSeqTail ->
        UnaryHistory dyadicLedger ->
          UnaryHistory realSeal ->
            UnaryHistory transport ->
              UnaryHistory replay ->
                Cont streamWindow regSeqTail streamRead ->
                  Cont streamRead dyadicLedger regularRead ->
                    Cont regularRead realSeal publicApprox ->
                      Cont transport replay toleranceRead ->
                        PkgSig bundle provenance pkg ->
                          PkgSig bundle localName pkg ->
                            SemanticNameCert
                                (fun row : BHist => hsame row publicApprox ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row streamWindow ∨ hsame row regSeqTail ∨
                                    hsame row dyadicLedger ∨ hsame row realSeal ∨
                                      hsame row publicApprox)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                                    PkgSig bundle localName pkg)
                                hsame ∧
                              UnaryHistory streamRead ∧ UnaryHistory regularRead ∧
                                UnaryHistory publicApprox := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro streamUnary regSeqUnary dyadicUnary realSealUnary transportUnary replayUnary
    streamRegSeqRoute streamDyadicRoute regularRealRoute transportReplayRoute
    provenancePkg localNamePkg
  have streamReadUnary : UnaryHistory streamRead :=
    unary_cont_closed streamUnary regSeqUnary streamRegSeqRoute
  have regularReadUnary : UnaryHistory regularRead :=
    unary_cont_closed streamReadUnary dyadicUnary streamDyadicRoute
  have publicApproxUnary : UnaryHistory publicApprox :=
    unary_cont_closed regularReadUnary realSealUnary regularRealRoute
  have _toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed transportUnary replayUnary transportReplayRoute
  have sourcePublic :
      (fun row : BHist => hsame row publicApprox ∧ UnaryHistory row) publicApprox := by
    exact ⟨hsame_refl publicApprox, publicApproxUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicApprox ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row streamWindow ∨ hsame row regSeqTail ∨ hsame row dyadicLedger ∨
              hsame row realSeal ∨ hsame row publicApprox)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicApprox sourcePublic
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, streamReadUnary, regularReadUnary, publicApproxUnary⟩

end BEDC.Derived.CauchyUp.L10SiblingDependency
