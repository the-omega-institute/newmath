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

theorem AuthorizedGeneratorRecursorLocalNameOutputExhaustion [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N outputRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont O A outputRead ->
      Cont outputRead N namedRead ->
      PkgSig bundle namedRead pkg ->
        SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row namedRead ∧ Cont O A outputRead ∧ Cont outputRead N namedRead)
          (fun row : BHist => hsame row namedRead ∧ PkgSig bundle namedRead pkg)
          hsame ∧ hsame H (append A C) ∧ UnaryHistory namedRead ∧
            PkgSig bundle namedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig SemanticNameCert hsame
  intro carrier outputRoute namedRoute namedPkg
  rcases carrier with
    ⟨_unaryI, _unaryE, _unaryM, _unaryB, _unaryD, unaryO, unaryA, sameTransport,
      _unaryC, _unaryP, _unaryG, unaryN, _contIEM, _contMBD, _contDOA,
      transportAppend, _provenancePkg⟩
  have outputUnary : UnaryHistory outputRead :=
    unary_cont_closed unaryO unaryA outputRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed outputUnary unaryN namedRoute
  have sourceNamed :
      (fun row : BHist => hsame row namedRead ∧ UnaryHistory row) namedRead := by
    exact ⟨hsame_refl namedRead, namedUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row namedRead ∧ Cont O A outputRead ∧ Cont outputRead N namedRead)
        (fun row : BHist => hsame row namedRead ∧ PkgSig bundle namedRead pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro namedRead sourceNamed
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
        exact ⟨source.left, outputRoute, namedRoute⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, namedPkg⟩
    }
  exact ⟨cert, transportAppend, namedUnary, namedPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
