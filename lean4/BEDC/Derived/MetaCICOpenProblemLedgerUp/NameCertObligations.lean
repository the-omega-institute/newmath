import BEDC.Derived.MetaCICOpenProblemLedgerUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
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
    (S C N U D E B H R P Q : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory PkgSig Cont
  UnaryHistory S ∧ UnaryHistory C ∧ UnaryHistory N ∧ UnaryHistory U ∧
    UnaryHistory D ∧ UnaryHistory E ∧ UnaryHistory B ∧ UnaryHistory H ∧
      UnaryHistory R ∧ UnaryHistory P ∧ UnaryHistory Q ∧
        Cont S U R ∧ Cont C U R ∧ Cont N B R ∧
          PkgSig bundle P pkg ∧ PkgSig bundle Q pkg

theorem MetaCICOpenProblemLedgerNameCertObligations [AskSetup] [PackageSetup]
    {S C N U D E B H R P Q : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICOpenProblemLedgerCarrier S C N U D E B H R P Q bundle pkg →
      SemanticNameCert
          (fun row : BHist => hsame row Q ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row C ∨ hsame row N ∨ hsame row U ∨
              hsame row D ∨ hsame row E ∨ hsame row B ∨ hsame row Q)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle Q pkg)
          hsame ∧
        Cont S U R ∧ Cont C U R ∧ Cont N B R ∧
          PkgSig bundle P pkg ∧ PkgSig bundle Q pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle SemanticNameCert UnaryHistory
  intro carrier
  obtain ⟨_subjectUnary, _confluenceUnary, _normalUnary, _substitutionUnary,
    _decidableUnary, _typedExampleUnary, _blockerUnary, _transportUnary, _routeUnary,
    _provenanceUnary, localNameUnary, subjectRoute, confluenceRoute, normalRoute,
    provenancePkg, localNamePkg⟩ := carrier
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row Q ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row C ∨ hsame row N ∨ hsame row U ∨
              hsame row D ∨ hsame row E ∨ hsame row B ∨ hsame row Q)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle Q pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro Q (And.intro (hsame_refl Q) localNameUnary)
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
          And.intro
            (hsame_trans (hsame_symm sameRows) source.left)
            (unary_transport source.right sameRows)
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, localNamePkg⟩
  }
  exact
    ⟨cert, subjectRoute, confluenceRoute, normalRoute, provenancePkg, localNamePkg⟩

end BEDC.Derived.MetaCICOpenProblemLedgerUp
