import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Derived.GapClosureBoundaryUp.TasteGate

namespace BEDC.Derived.GapClosureBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem GapClosureBoundaryConsumerExactnessPackage [AskSetup] [PackageSetup]
    {G S R H C P N sourceRead refusalRead sourceConsumer refusalConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory G ->
      UnaryHistory S ->
        UnaryHistory R ->
          UnaryHistory H ->
            Cont G S sourceRead ->
              Cont sourceRead H sourceConsumer ->
                Cont G R refusalRead ->
                  Cont refusalRead H refusalConsumer ->
                    PkgSig bundle sourceConsumer pkg ->
                      PkgSig bundle refusalConsumer pkg ->
                        SemanticNameCert
                            (fun row : BHist =>
                              (hsame row sourceConsumer ∨ hsame row refusalConsumer) ∧
                                ∃ packet : GapClosureBoundaryUp,
                                  packet = GapClosureBoundaryUp.mk G S R H C P N)
                            (fun row : BHist =>
                              (hsame row sourceConsumer ∧ Cont G S sourceRead) ∨
                                (hsame row refusalConsumer ∧ Cont G R refusalRead))
                            (fun row : BHist =>
                              (hsame row sourceConsumer ∧ PkgSig bundle sourceConsumer pkg) ∨
                                (hsame row refusalConsumer ∧ PkgSig bundle refusalConsumer pkg))
                            hsame ∧
                          UnaryHistory sourceRead ∧ UnaryHistory sourceConsumer ∧
                            UnaryHistory refusalRead ∧ UnaryHistory refusalConsumer ∧
                              Cont G S sourceRead ∧ Cont sourceRead H sourceConsumer ∧
                                Cont G R refusalRead ∧ Cont refusalRead H refusalConsumer := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro unaryG unaryS unaryR unaryH sourceRoute sourceConsumerRoute refusalRoute
    refusalConsumerRoute sourcePkg refusalPkg
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed unaryG unaryS sourceRoute
  have sourceConsumerUnary : UnaryHistory sourceConsumer :=
    unary_cont_closed sourceReadUnary unaryH sourceConsumerRoute
  have refusalReadUnary : UnaryHistory refusalRead :=
    unary_cont_closed unaryG unaryR refusalRoute
  have refusalConsumerUnary : UnaryHistory refusalConsumer :=
    unary_cont_closed refusalReadUnary unaryH refusalConsumerRoute
  have sourceAtConsumer :
      (hsame sourceConsumer sourceConsumer ∨ hsame sourceConsumer refusalConsumer) ∧
        ∃ packet : GapClosureBoundaryUp, packet = GapClosureBoundaryUp.mk G S R H C P N :=
    ⟨Or.inl (hsame_refl sourceConsumer),
      Exists.intro (GapClosureBoundaryUp.mk G S R H C P N) rfl⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row sourceConsumer ∨ hsame row refusalConsumer) ∧
              ∃ packet : GapClosureBoundaryUp,
                packet = GapClosureBoundaryUp.mk G S R H C P N)
          (fun row : BHist =>
            (hsame row sourceConsumer ∧ Cont G S sourceRead) ∨
              (hsame row refusalConsumer ∧ Cont G R refusalRead))
          (fun row : BHist =>
            (hsame row sourceConsumer ∧ PkgSig bundle sourceConsumer pkg) ∨
              (hsame row refusalConsumer ∧ PkgSig bundle refusalConsumer pkg))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sourceConsumer sourceAtConsumer
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
        constructor
        · cases source.left with
          | inl sameSource =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameSource)
          | inr sameRefusal =>
              exact Or.inr (hsame_trans (hsame_symm sameRows) sameRefusal)
        · exact source.right
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameSource =>
          exact Or.inl ⟨sameSource, sourceRoute⟩
      | inr sameRefusal =>
          exact Or.inr ⟨sameRefusal, refusalRoute⟩
    ledger_sound := by
      intro _row source
      cases source.left with
      | inl sameSource =>
          exact Or.inl ⟨sameSource, sourcePkg⟩
      | inr sameRefusal =>
          exact Or.inr ⟨sameRefusal, refusalPkg⟩
  }
  exact
    ⟨cert, sourceReadUnary, sourceConsumerUnary, refusalReadUnary, refusalConsumerUnary,
      sourceRoute, sourceConsumerRoute, refusalRoute, refusalConsumerRoute⟩

end BEDC.Derived.GapClosureBoundaryUp
