import BEDC.Derived.NoGlobalSynchronizationLedgerUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.NoGlobalSynchronizationLedgerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.Meta.TasteGate

theorem NoGlobalSynchronizationLedgerUp_namecert_obligations [AskSetup] [PackageSetup]
    {H0 H1 R B O I K S C P N localRead boundaryRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont H0 H1 localRead →
      Cont R B boundaryRead →
        Cont O I consumerRead →
          PkgSig bundle P pkg →
            SemanticNameCert
                (fun row : BHist =>
                  hsame row N ∧
                    FieldFaithful.fields
                        (NoGlobalSynchronizationLedgerUp.mk H0 H1 R B O I K S C P N) =
                      [H0, H1, R, B, O, I, K, S, C, P, N])
                (fun row : BHist =>
                  hsame row R ∨ hsame row B ∨ hsame row O ∨ hsame row I ∨
                    hsame row K ∨ Cont H0 H1 localRead ∨ Cont R B boundaryRead)
                (fun row : BHist => hsame row N ∧ PkgSig bundle P pkg)
                hsame ∧
              FieldFaithful.fields
                  (NoGlobalSynchronizationLedgerUp.mk H0 H1 R B O I K S C P N) =
                [H0, H1, R, B, O, I, K, S, C, P, N] ∧
                Cont H0 H1 localRead ∧ Cont R B boundaryRead ∧
                  Cont O I consumerRead ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert FieldFaithful hsame
  intro localRoute boundaryRoute consumerRoute pkgSig
  have fields :
      FieldFaithful.fields
          (NoGlobalSynchronizationLedgerUp.mk H0 H1 R B O I K S C P N) =
        [H0, H1, R, B, O, I, K, S, C, P, N] := by
    rfl
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row N ∧
              FieldFaithful.fields
                  (NoGlobalSynchronizationLedgerUp.mk H0 H1 R B O I K S C P N) =
                [H0, H1, R, B, O, I, K, S, C, P, N])
          (fun row : BHist =>
            hsame row R ∨ hsame row B ∨ hsame row O ∨ hsame row I ∨
              hsame row K ∨ Cont H0 H1 localRead ∨ Cont R B boundaryRead)
          (fun row : BHist => hsame row N ∧ PkgSig bundle P pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro N ⟨hsame_refl N, fields⟩
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
          exact ⟨hsame_trans (hsame_symm same) source.left, source.right⟩
      }
      pattern_sound := by
        intro _row _source
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl localRoute)))))
      ledger_sound := by
        intro _row source
        exact ⟨source.left, pkgSig⟩
    }
  exact ⟨cert, fields, localRoute, boundaryRoute, consumerRoute, pkgSig⟩

end BEDC.Derived.NoGlobalSynchronizationLedgerUp
