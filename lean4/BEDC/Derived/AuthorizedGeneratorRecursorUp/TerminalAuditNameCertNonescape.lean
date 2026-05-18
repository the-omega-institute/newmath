import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier
import BEDC.FKernel.NameCert
import BEDC.FKernel.Sig

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorTerminalAuditNameCertNonescape [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N outputRead auditRead boundaryRead nameRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont O A outputRead ->
        Cont outputRead A auditRead ->
          Cont outputRead G boundaryRead ->
            Cont outputRead N nameRead ->
              PkgSig bundle nameRead pkg ->
                SemanticNameCert
                    (fun row : BHist =>
                      AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ∧
                        hsame row nameRead)
                    (fun row : BHist =>
                      hsame row O ∨ hsame row A ∨ hsame row G ∨ hsame row N ∨
                        hsame row nameRead)
                    (fun row : BHist =>
                      PkgSig bundle P pkg ∧ PkgSig bundle nameRead pkg ∧
                        hsame row nameRead)
                    hsame ∧
                  UnaryHistory outputRead ∧ UnaryHistory auditRead ∧
                    UnaryHistory boundaryRead ∧ UnaryHistory nameRead ∧
                      Cont O A outputRead ∧ Cont outputRead A auditRead ∧
                        Cont outputRead G boundaryRead ∧ Cont outputRead N nameRead ∧
                          hsame H (append A C) ∧ PkgSig bundle P pkg ∧
                            PkgSig bundle nameRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame
  intro carrier outputCont auditCont boundaryCont nameCont namePkg
  rcases carrier with
    ⟨unaryI, unaryE, unaryM, unaryB, unaryD, unaryO, unaryA, unaryH, unaryC,
      unaryP, unaryG, unaryN, contIEM, contMBD, contDOA, sameTransport,
      provenancePkg⟩
  have outputUnary : UnaryHistory outputRead :=
    unary_cont_closed unaryO unaryA outputCont
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed outputUnary unaryA auditCont
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed outputUnary unaryG boundaryCont
  have nameUnary : UnaryHistory nameRead :=
    unary_cont_closed outputUnary unaryN nameCont
  have carrierAgain :
      AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg := by
    exact
      ⟨unaryI, unaryE, unaryM, unaryB, unaryD, unaryO, unaryA, unaryH, unaryC,
        unaryP, unaryG, unaryN, contIEM, contMBD, contDOA, sameTransport, provenancePkg⟩
  have sourceName :
      (fun row : BHist =>
        AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ∧
          hsame row nameRead) nameRead := by
    exact ⟨carrierAgain, hsame_refl nameRead⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ∧
              hsame row nameRead)
          (fun row : BHist =>
            hsame row O ∨ hsame row A ∨ hsame row G ∨ hsame row N ∨
              hsame row nameRead)
          (fun row : BHist =>
            PkgSig bundle P pkg ∧ PkgSig bundle nameRead pkg ∧ hsame row nameRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro nameRead sourceName
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
        intro _row source
        exact Or.inr (Or.inr (Or.inr (Or.inr source.right)))
      ledger_sound := by
        intro _row source
        exact ⟨provenancePkg, namePkg, source.right⟩
    }
  exact
    ⟨cert, outputUnary, auditUnary, boundaryUnary, nameUnary, outputCont, auditCont,
      boundaryCont, nameCont, sameTransport, provenancePkg, namePkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
