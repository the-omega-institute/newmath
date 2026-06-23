import BEDC.Derived.FinitePrefixAutomatonUp.Classifier
import BEDC.Derived.FinitePrefixAutomatonUp.Determinacy
import BEDC.FKernel.Ask
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.FinitePrefixAutomatonUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FinitePrefixAutomatonCarrier_prefix_run_displayed_determinism [AskSetup] [PackageSetup]
    {Q q0 A T W R R' E E' H C P N endpointCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory q0 ->
      UnaryHistory W ->
        UnaryHistory H ->
          Cont q0 W R ->
            Cont q0 W R' ->
              Cont R H E ->
                Cont R' H E' ->
                  PkgSig bundle E pkg ->
                    SemanticNameCert
                        (fun row : BHist => (hsame row E ∨ hsame row E') ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row Q ∨ hsame row q0 ∨ hsame row W ∨ hsame row R ∨
                            hsame row R' ∨ hsame row E ∨ hsame row E')
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont q0 W R ∧ Cont q0 W R' ∧ Cont R H E ∧
                            Cont R' H E' ∧ PkgSig bundle E pkg)
                        hsame ∧
                      hsame R R' ∧ hsame E E' ∧ UnaryHistory R ∧ UnaryHistory R' ∧
                        UnaryHistory E ∧ UnaryHistory E' := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro q0Unary wordUnary endpointUnary runRoute runRoute' endpointRoute endpointRoute' pkgRead
  have runPack :
      hsame R R' ∧ UnaryHistory R ∧ UnaryHistory R' ∧ UnaryHistory E ∧ UnaryHistory E' :=
    FinitePrefixAutomatonCarrier_prefix_run_determinacy q0Unary wordUnary endpointUnary
      runRoute runRoute' endpointRoute endpointRoute'
  have sameEndpoint : hsame E E' :=
    cont_respects_hsame runPack.left (hsame_refl H) endpointRoute endpointRoute'
  have cert :
      SemanticNameCert
          (fun row : BHist => (hsame row E ∨ hsame row E') ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Q ∨ hsame row q0 ∨ hsame row W ∨ hsame row R ∨ hsame row R' ∨
              hsame row E ∨ hsame row E')
          (fun row : BHist =>
            UnaryHistory row ∧ Cont q0 W R ∧ Cont q0 W R' ∧ Cont R H E ∧
              Cont R' H E' ∧ PkgSig bundle E pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro E ⟨Or.inl (hsame_refl E), runPack.right.right.right.left⟩
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
          | inl sameE =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameE)
          | inr sameE' =>
              exact Or.inr (hsame_trans (hsame_symm sameRows) sameE')
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameE =>
          exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl sameE
      | inr sameE' =>
          exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr sameE'
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, runRoute, runRoute', endpointRoute, endpointRoute', pkgRead⟩
  }
  exact
    ⟨cert, runPack.left, sameEndpoint, runPack.right.left, runPack.right.right.left,
      runPack.right.right.right.left, runPack.right.right.right.right⟩

end BEDC.Derived.FinitePrefixAutomatonUp
