import BEDC.Derived.SetlikeUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SetlikeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def SetlikeExtensionalSubsetCarrier [AskSetup] [PackageSetup] (S : SetlikeUp)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  ∃ M Q I R E H C P N subsetRead extensionalRead namedRead : BHist,
    setlikeFields S = [M, Q, I, R, E, H, C, P, N] ∧
      Cont M Q subsetRead ∧
        Cont subsetRead I extensionalRead ∧
          Cont extensionalRead E namedRead ∧
            PkgSig bundle P pkg ∧
              Nonempty
                (SemanticNameCert
                  (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row M ∨ hsame row Q ∨ hsame row I ∨ hsame row E ∨
                      hsame row namedRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont subsetRead I extensionalRead ∧
                      Cont extensionalRead E namedRead ∧ PkgSig bundle P pkg)
                  hsame)

theorem SetlikeExtensionalSubsetCarrier_route_closed [AskSetup] [PackageSetup]
    (S : SetlikeUp) {M Q I R E H C P N subsetRead extensionalRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    setlikeFields S = [M, Q, I, R, E, H, C, P, N] →
      UnaryHistory M →
        UnaryHistory Q →
          UnaryHistory I →
            UnaryHistory E →
              Cont M Q subsetRead →
                Cont subsetRead I extensionalRead →
                  Cont extensionalRead E namedRead →
                    PkgSig bundle P pkg →
                      SetlikeExtensionalSubsetCarrier S bundle pkg ∧
                        UnaryHistory subsetRead ∧
                          UnaryHistory extensionalRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: SetlikeUp setlikeFields BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro fields mUnary qUnary iUnary eUnary subsetRoute extensionalRoute namedRoute
    packageRead
  have subsetUnary : UnaryHistory subsetRead :=
    unary_cont_closed mUnary qUnary subsetRoute
  have extensionalUnary : UnaryHistory extensionalRead :=
    unary_cont_closed subsetUnary iUnary extensionalRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed extensionalUnary eUnary namedRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row M ∨ hsame row Q ∨ hsame row I ∨ hsame row E ∨
            hsame row namedRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont subsetRead I extensionalRead ∧
            Cont extensionalRead E namedRead ∧ PkgSig bundle P pkg)
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, extensionalRoute, namedRoute, packageRead⟩
  }
  exact
    ⟨⟨M, Q, I, R, E, H, C, P, N, subsetRead, extensionalRead, namedRead, fields,
        subsetRoute, extensionalRoute, namedRoute, packageRead, ⟨cert⟩⟩,
      subsetUnary, extensionalUnary, namedUnary⟩

end BEDC.Derived.SetlikeUp
