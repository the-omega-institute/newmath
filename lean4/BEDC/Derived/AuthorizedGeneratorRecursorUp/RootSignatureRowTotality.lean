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

theorem AuthorizedGeneratorRecursorRootSignatureRowTotality [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N rootRead auditRead boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg →
      Cont I E rootRead →
        Cont O A auditRead →
          Cont G N boundaryRead →
            PkgSig bundle boundaryRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N
                      bundle pkg ∧ hsame row N)
                  (fun row : BHist =>
                    hsame row I ∨ hsame row E ∨ hsame row M ∨ hsame row B ∨
                      hsame row D ∨ hsame row O ∨ hsame row A ∨ hsame row H ∨
                        hsame row C ∨ hsame row P ∨ hsame row G ∨ hsame row N)
                  (fun row : BHist =>
                    PkgSig bundle P pkg ∧ PkgSig bundle boundaryRead pkg ∧ hsame row N)
                  hsame ∧
                UnaryHistory rootRead ∧ UnaryHistory auditRead ∧
                  UnaryHistory boundaryRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert UnaryHistory Cont hsame
  intro carrier rootCont auditCont boundaryCont boundaryPkg
  rcases carrier with
    ⟨unaryI, unaryE, unaryM, unaryB, unaryD, unaryO, unaryA, unaryH, unaryC,
      unaryP, unaryG, unaryN, contIEM, contMBD, contDOA, sameTransport,
      provenancePkg⟩
  have carrier :
      AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg := by
    exact
      ⟨unaryI, unaryE, unaryM, unaryB, unaryD, unaryO, unaryA, unaryH, unaryC,
        unaryP, unaryG, unaryN, contIEM, contMBD, contDOA, sameTransport,
        provenancePkg⟩
  have rootUnary : UnaryHistory rootRead := unary_cont_closed unaryI unaryE rootCont
  have auditUnary : UnaryHistory auditRead := unary_cont_closed unaryO unaryA auditCont
  have boundaryUnary : UnaryHistory boundaryRead := unary_cont_closed unaryG unaryN boundaryCont
  have sourceN :
      (fun row : BHist =>
        AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ∧
          hsame row N) N := by
    exact ⟨carrier, hsame_refl N⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ∧
              hsame row N)
          (fun row : BHist =>
            hsame row I ∨ hsame row E ∨ hsame row M ∨ hsame row B ∨
              hsame row D ∨ hsame row O ∨ hsame row A ∨ hsame row H ∨
                hsame row C ∨ hsame row P ∨ hsame row G ∨ hsame row N)
          (fun row : BHist =>
            PkgSig bundle P pkg ∧ PkgSig bundle boundaryRead pkg ∧ hsame row N)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro N sourceN
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
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr source.right))))))))))
      ledger_sound := by
        intro _row source
        exact ⟨provenancePkg, boundaryPkg, source.right⟩
    }
  exact ⟨cert, rootUnary, auditUnary, boundaryUnary⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
