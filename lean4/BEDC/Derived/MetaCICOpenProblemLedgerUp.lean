import BEDC.Derived.MetaCICOpenProblemLedgerUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MetaCICOpenProblemLedgerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def MetaCICOpenProblemLedgerCarrier [AskSetup] [PackageSetup]
    (S C N U D E B H R P Q : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory S ∧ UnaryHistory C ∧ UnaryHistory N ∧ UnaryHistory U ∧
    UnaryHistory D ∧ UnaryHistory E ∧ UnaryHistory B ∧ UnaryHistory H ∧
      UnaryHistory R ∧ UnaryHistory P ∧ UnaryHistory Q ∧ Cont S C N ∧
        Cont U D E ∧ Cont B H R ∧ PkgSig bundle P pkg ∧ PkgSig bundle Q pkg

theorem MetaCICOpenProblemLedger_namecert_obligations [AskSetup] [PackageSetup]
    {S C N U D E B H R P Q ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICOpenProblemLedgerCarrier S C N U D E B H R P Q bundle pkg ->
      Cont R P ledgerRead ->
        PkgSig bundle ledgerRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row S ∨ hsame row C ∨ hsame row N ∨ hsame row U ∨
                  hsame row D ∨ hsame row E ∨ hsame row B ∨ hsame row H ∨
                    hsame row R ∨ hsame row ledgerRead)
              (fun row : BHist => hsame row ledgerRead ∧ PkgSig bundle ledgerRead pkg)
              hsame ∧
            UnaryHistory S ∧ UnaryHistory C ∧ UnaryHistory N ∧ UnaryHistory U ∧
              UnaryHistory D ∧ UnaryHistory E ∧ UnaryHistory B ∧ UnaryHistory H ∧
                UnaryHistory R ∧ UnaryHistory ledgerRead ∧ Cont R P ledgerRead ∧
                  PkgSig bundle Q pkg ∧ PkgSig bundle ledgerRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert UnaryHistory
  intro carrier ledgerRoute ledgerPkg
  obtain ⟨sUnary, cUnary, nUnary, uUnary, dUnary, eUnary, bUnary, hUnary, rUnary,
    pUnary, _qUnary, _subjectConfluenceName, _substitutionDecidableExample,
    _blockerHandoffReplay, _provenancePkg, localNamePkg⟩ := carrier
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed rUnary pUnary ledgerRoute
  have sourceAtLedger : hsame ledgerRead ledgerRead ∧ UnaryHistory ledgerRead :=
    ⟨hsame_refl ledgerRead, ledgerUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row C ∨ hsame row N ∨ hsame row U ∨
              hsame row D ∨ hsame row E ∨ hsame row B ∨ hsame row H ∨
                hsame row R ∨ hsame row ledgerRead)
          (fun row : BHist => hsame row ledgerRead ∧ PkgSig bundle ledgerRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro ledgerRead sourceAtLedger
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr (Or.inr (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, ledgerPkg⟩
  }
  exact
    ⟨cert, sUnary, cUnary, nUnary, uUnary, dUnary, eUnary, bUnary, hUnary, rUnary,
      ledgerUnary, ledgerRoute, localNamePkg, ledgerPkg⟩

end BEDC.Derived.MetaCICOpenProblemLedgerUp
