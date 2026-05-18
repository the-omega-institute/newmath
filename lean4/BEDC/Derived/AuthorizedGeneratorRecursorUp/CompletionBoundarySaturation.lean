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

theorem AuthorizedGeneratorRecursorCompletionBoundarySaturation [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N streamRead regseqRead realRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg →
      Cont O H streamRead →
        Cont streamRead C regseqRead →
          Cont regseqRead G realRead →
            Cont realRead N completionRead →
              PkgSig bundle completionRead pkg →
                SemanticNameCert
                  (fun row : BHist =>
                    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ∧
                      hsame row completionRead)
                  (fun row : BHist =>
                    Cont O H streamRead ∧ Cont streamRead C regseqRead ∧
                      Cont regseqRead G realRead ∧ Cont realRead N row)
                  (fun row : BHist => UnaryHistory row ∧ PkgSig bundle completionRead pkg)
                  hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier outputStream streamRegseq regseqReal realCompletion completionPkg
  rcases carrier with
    ⟨unaryI, unaryE, unaryM, unaryB, unaryD, unaryO, unaryA, unaryH, unaryC,
      unaryP, unaryG, unaryN, branchRoute, descentRoute, outputRoute, transportSame,
      provenancePkg⟩
  have retainedCarrier :
      AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg :=
    ⟨unaryI, unaryE, unaryM, unaryB, unaryD, unaryO, unaryA, unaryH, unaryC, unaryP,
      unaryG, unaryN, branchRoute, descentRoute, outputRoute, transportSame, provenancePkg⟩
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed unaryO unaryH outputStream
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed streamUnary unaryC streamRegseq
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed regseqUnary unaryG regseqReal
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed realUnary unaryN realCompletion
  have sourceCompletion :
      (fun row : BHist =>
        AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ∧
          hsame row completionRead) completionRead := by
    exact ⟨retainedCarrier, hsame_refl completionRead⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro completionRead sourceCompletion
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
        exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
    }
    pattern_sound := by
      intro _row source
      cases source.right
      exact ⟨outputStream, streamRegseq, regseqReal, realCompletion⟩
    ledger_sound := by
      intro _row source
      cases source.right
      exact ⟨completionUnary, completionPkg⟩
  }

end BEDC.Derived.AuthorizedGeneratorRecursorUp
