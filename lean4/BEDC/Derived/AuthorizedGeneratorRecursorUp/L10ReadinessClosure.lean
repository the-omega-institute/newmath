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

theorem AuthorizedGeneratorRecursorL10ReadinessClosure [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N streamRead regseqRead realRead metacicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont O A streamRead ->
        Cont streamRead C regseqRead ->
          Cont regseqRead G realRead ->
            Cont realRead N metacicRead ->
              PkgSig bundle metacicRead pkg ->
                SemanticNameCert
                  (fun row : BHist =>
                    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ∧
                      hsame row metacicRead)
                  (fun row : BHist =>
                    Cont O A streamRead ∧ Cont streamRead C regseqRead ∧
                      Cont regseqRead G realRead ∧ Cont realRead N row)
                  (fun row : BHist => UnaryHistory row ∧ PkgSig bundle metacicRead pkg)
                  hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont SemanticNameCert hsame
  intro carrier outputStream streamRegseq regseqReal realMeta metaPkg
  rcases carrier with
    ⟨unaryI, unaryE, unaryM, unaryB, unaryD, unaryO, unaryA, _unaryH, unaryC,
      _unaryP, unaryG, unaryN, contIEM, contMBD, contDOA, sameTransport,
      provenancePkg⟩
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed unaryO unaryA outputStream
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed streamUnary unaryC streamRegseq
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed regseqUnary unaryG regseqReal
  have metaUnary : UnaryHistory metacicRead :=
    unary_cont_closed realUnary unaryN realMeta
  have carrierCopy :
      AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg := by
    exact
      ⟨unaryI, unaryE, unaryM, unaryB, unaryD, unaryO, unaryA, _unaryH, unaryC,
        _unaryP, unaryG, unaryN, contIEM, contMBD, contDOA, sameTransport,
        provenancePkg⟩
  have sourceMeta :
      (fun row : BHist =>
        AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ∧
          hsame row metacicRead) metacicRead := by
    exact ⟨carrierCopy, hsame_refl metacicRead⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro metacicRead sourceMeta
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
        exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
    }
    pattern_sound := by
      intro row source
      exact
        ⟨outputStream, streamRegseq, regseqReal,
          cont_result_hsame_transport realMeta (hsame_symm source.right)⟩
    ledger_sound := by
      intro row source
      have rowUnary : UnaryHistory row :=
        unary_transport metaUnary (hsame_symm source.right)
      exact ⟨rowUnary, metaPkg⟩
  }

end BEDC.Derived.AuthorizedGeneratorRecursorUp
